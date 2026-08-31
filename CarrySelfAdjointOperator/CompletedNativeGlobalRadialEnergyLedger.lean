import CarrySelfAdjointOperator.CompletedNativeCausalLegChiralBridge
import CarrySelfAdjointOperator.CompletedC3AmbientRadialTiltSamplePositivity
import Mathlib.Tactic

/-!
# Global radial energy of the completed center--leg ledger

The full ambient C3 response has a positive diagonal Green boundary.  The
completed native `(F,-F')` wedge is the derivative of one global transverse
modulus energy.  This module places those two facts in the same diagonal
identity while retaining the complete ambient correction ledger.

No correction channel is forced to vanish.  Instead, the exact remaining sign
condition is exposed as a comparison between the correction ledger and the
positive ambient energy.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

/-- On the upper half-plane diagonal, the ambient boundary is exactly twice
the height times the squared norm of the full source-matched response. -/
theorem canonicalCompletedC3AmbientBoundaryReadout_diagonal_im_eq_energy
    {z : ℂ} (hzIm : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    (canonicalCompletedC3AmbientBoundaryReadout
        z z hzHalf hzHalf).im =
      2 * z.im *
        ‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 := by
  rw [canonicalCompletedC3AmbientBoundaryReadout_eq_kernel
    z z hzIm hzIm hzHalf hzHalf]
  change
    ((z - conj z) * inner ℂ
      (canonicalCompletedC3AmbientResponseState z hzHalf)
      (canonicalCompletedC3AmbientResponseState z hzHalf)).im = _
  rw [inner_self_eq_norm_sq_to_K]
  simp [Complex.mul_im]
  norm_cast
  ring

/-- Positivity of the full ambient diagonal boundary is unconditional once the
point lies above the real height axis. -/
theorem canonicalCompletedC3AmbientBoundaryReadout_diagonal_im_nonneg
    {z : ℂ} (hzIm : 0 < z.im)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    0 ≤ (canonicalCompletedC3AmbientBoundaryReadout
      z z hzHalf hzHalf).im := by
  rw [canonicalCompletedC3AmbientBoundaryReadout_diagonal_im_eq_energy
    (ne_of_gt hzIm) hzHalf]
  positivity

/-- On the diagonal, the completed TFVD Wronskian is exactly any honest
local/cross/residual presentation of the completed native scalar ledger. -/
theorem canonicalC3BracketTfvdCompletedWronskianReadout_diagonal_eq_localLegLedger
    {ι : Type*} [Fintype ι]
    (M : ℕ) {z : ℂ} (hzDomain : z ∈ completedNativeHeightDomain)
    (legs : ReflectedBoundarySynthesisData ι) :
    canonicalC3BracketTfvdCompletedWronskianReadout M z z =
      completedNativeFNegFPrimeLocalLegLedger z legs := by
  rw [canonicalC3BracketTfvdCompletedWronskianReadout_eq_F_negFprime
    M hzDomain hzDomain]
  rw [completedNativeFNegFPrimeLocalLegLedger_eq_scalarBoundaryWedge]
  simp [completedGreenWronskian, scalarBoundaryWedge,
    completedNativeOperatorBoundaryCompanion]
  ring

/-- Exact source-matched diagonal square on the admissible radial grid.  The
positive ambient boundary is the completed native ledger plus the whole
four-channel correction ledger. -/
theorem completedNativeLocalLegLedger_add_ambientCorrection_eq_boundary
    {ι : Type*} [Fintype ι]
    (M k N : ℕ) (i : Fin N)
    (legs : ReflectedBoundarySynthesisData ι) :
    completedNativeFNegFPrimeLocalLegLedger
          (canonicalCompletedC3AmbientRadialTiltPoint k N i) legs +
        canonicalCompletedC3AmbientRadialWronskianCorrectionLedger k N i i =
      canonicalCompletedC3AmbientBoundaryReadout
        (canonicalCompletedC3AmbientRadialTiltPoint k N i)
        (canonicalCompletedC3AmbientRadialTiltPoint k N i)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i) := by
  have hsquare :=
    canonicalCompletedC3AmbientRadialBoundary_sub_wronskian_eq_ledger
      M k N i i
  have hwedge :=
    canonicalC3BracketTfvdCompletedWronskianReadout_diagonal_eq_localLegLedger
      (ι := ι) M
      (canonicalCompletedC3AmbientRadialTiltPoint_mem_genuineCriticalStrip
        k N i) legs
  rw [hwedge] at hsquare
  rw [← hsquare]
  ring

/-- Imaginary-part form of the same square.  This is route B with every
local, cross, residual, completion, and ambient correction channel retained. -/
theorem completedNativeLocalLegLedger_im_add_ambientCorrection_im_eq_energy
    {ι : Type*} [Fintype ι]
    (M k N : ℕ) (i : Fin N)
    (legs : ReflectedBoundarySynthesisData ι) :
    (completedNativeFNegFPrimeLocalLegLedger
        (canonicalCompletedC3AmbientRadialTiltPoint k N i) legs).im +
      (canonicalCompletedC3AmbientRadialWronskianCorrectionLedger
        k N i i).im =
      2 * (canonicalCompletedC3AmbientRadialTiltPoint k N i).im *
        ‖canonicalCompletedC3AmbientResponseState
          (canonicalCompletedC3AmbientRadialTiltPoint k N i)
          (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i)‖ ^ 2 := by
  have hsum := congrArg Complex.im
    (completedNativeLocalLegLedger_add_ambientCorrection_eq_boundary
      (ι := ι) M k N i legs)
  rw [canonicalCompletedC3AmbientBoundaryReadout_diagonal_im_eq_energy
    (canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k N i)
    (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i)] at hsum
  simpa only [Complex.add_im] using hsum

/-- The exact inequality left by the positive ambient factorization.  Native
route-B positivity holds precisely when the correction ledger consumes no more
than the full ambient diagonal energy. -/
theorem completedNativeLocalLegLedger_im_nonneg_iff_ambientCorrection_le_energy
    {ι : Type*} [Fintype ι]
    (M k N : ℕ) (i : Fin N)
    (legs : ReflectedBoundarySynthesisData ι) :
    0 ≤ (completedNativeFNegFPrimeLocalLegLedger
        (canonicalCompletedC3AmbientRadialTiltPoint k N i) legs).im ↔
      (canonicalCompletedC3AmbientRadialWronskianCorrectionLedger
          k N i i).im ≤
        2 * (canonicalCompletedC3AmbientRadialTiltPoint k N i).im *
          ‖canonicalCompletedC3AmbientResponseState
            (canonicalCompletedC3AmbientRadialTiltPoint k N i)
            (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i)‖ ^ 2 := by
  have henergy :=
    completedNativeLocalLegLedger_im_add_ambientCorrection_im_eq_energy
      (ι := ι) M k N i legs
  constructor <;> intro h <;> linarith

/-- Differential spelling of the same exact gate.  Mere convergence of the
correction ledger to zero is not enough: its imaginary part must be controlled
at the first radial order displayed on the right. -/
theorem completedNativeVerticalModulusEnergy_deriv_nonneg_iff_ambientCorrection_le_energy
    {ι : Type*} [Fintype ι]
    (M k N : ℕ) (i : Fin N)
    (legs : ReflectedBoundarySynthesisData ι) :
    0 ≤ deriv
        (completedNativeVerticalModulusEnergy
          (canonicalCompletedC3AmbientRadialTiltPoint k N i)) 0 ↔
      (canonicalCompletedC3AmbientRadialWronskianCorrectionLedger
          k N i i).im ≤
        2 * (canonicalCompletedC3AmbientRadialTiltPoint k N i).im *
          ‖canonicalCompletedC3AmbientResponseState
            (canonicalCompletedC3AmbientRadialTiltPoint k N i)
            (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i)‖ ^ 2 := by
  rw [(hasDerivAt_completedNativeVerticalModulusEnergy_eq_localLegLedger
    (canonicalCompletedC3AmbientRadialTiltPoint_mem_genuineCriticalStrip
      k N i) legs).deriv]
  exact
    completedNativeLocalLegLedger_im_nonneg_iff_ambientCorrection_le_energy
      M k N i legs

/-- Final diagonal `dslope` form on the ambient radial grid.  It uses no Gram
comparison: both sides are reduced to the same complete scalar energy ledger. -/
theorem
    completedNativePolarizedDslopeKernel_diagonal_re_nonneg_iff_ambientCorrection_le_energy
    {ι : Type*} [Fintype ι]
    (M k N : ℕ) (i : Fin N)
    (legs : ReflectedBoundarySynthesisData ι)
    (hF : completedNativeOperatorCharacteristic
      (canonicalCompletedC3AmbientRadialTiltPoint k N i) ≠ 0) :
    0 ≤ (canonicalCompletedNativePolarizedDslopeKernel
        (canonicalCompletedC3AmbientRadialTiltPoint k N i)
        (canonicalCompletedC3AmbientRadialTiltPoint k N i)).re ↔
      (canonicalCompletedC3AmbientRadialWronskianCorrectionLedger
          k N i i).im ≤
        2 * (canonicalCompletedC3AmbientRadialTiltPoint k N i).im *
          ‖canonicalCompletedC3AmbientResponseState
            (canonicalCompletedC3AmbientRadialTiltPoint k N i)
            (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i)‖ ^ 2 := by
  rw [completedNativePolarizedDslopeKernel_diagonal_re_nonneg_iff_localLegLedger
    legs
    (canonicalCompletedC3AmbientRadialTiltPoint_mem_genuineCriticalStrip k N i)
    hF (canonicalCompletedC3AmbientRadialTiltPoint_im_pos k N i)]
  exact
    completedNativeLocalLegLedger_im_nonneg_iff_ambientCorrection_le_energy
      M k N i legs

end

end CarrySelfAdjointOperator
