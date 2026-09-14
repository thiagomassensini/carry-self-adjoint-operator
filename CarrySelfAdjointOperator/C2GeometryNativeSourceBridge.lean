import CarrySelfAdjointOperator.C2LiteralCameraAllOrderJetCrosswalk
import CarrySelfAdjointOperator.PrimeDepthTfvdLogJetCrosswalk

/-!
# Exact C2 geometry-to-native source bridge

This module packages the geometric content of the C2 pushforward note before
any Hankel matrix, whitening, Jacobi matrix, or height operator is introduced.
The aligned camera centre is identified with its odd-core dyadic fibre, the two
incidence legs are the two neighbouring fibre points, and the logarithm splits
into the current dyadic depth plus the prime-depth ledger of the odd core.

The finite all-order readout is then the seed plus the exact sum of those
fibre brackets.  These are source identities: they do not define a positive
proxy and they do not assert the still-open material clock-boundary
calibration.
-/

open scoped BigOperators

namespace CarrySelfAdjointOperator

open CPFormal.Carry.C2
open CPFormal.Carry.Cp
open CPFormal.Carry.Positional
open ProjectiveDepth
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Camera.FiniteBridge

noncomputable section

/-! ## The geometric fibre identity -/

/-- One aligned C2 camera cell, written entirely in its native dyadic fibre
coordinates.  The last equality is the Green/Newton seed decomposition of the
logarithmic centre amplitude, with the odd core written by the exact prime
depth ledger. -/
theorem canonicalC2Geometry_nativeSourceChain (j : ℕ) :
    4 * (j + 1) =
        2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j ∧
      ((leftIncidence j).1.2 : ℝ) =
        c2FiberPoint (c2AlignedIndexCore j) (-1)
          (c2AlignedIndexDepth j) ∧
      ((rightIncidence j).1.2 : ℝ) =
        c2FiberPoint (c2AlignedIndexCore j) 1
          (c2AlignedIndexDepth j) ∧
      CPFormal.Carry.C2.effectiveDepth (leftIncidence j).1.2 =
        c2AlignedIndexDepth j ∧
      CPFormal.Carry.C2.effectiveDepth (rightIncidence j).1.2 =
        c2AlignedIndexDepth j ∧
      Real.log ((4 * (j + 1) : ℕ) : ℝ) =
        (c2AlignedIndexDepth j : ℝ) * Real.log 2 +
          primeDepthLogLedger (c2AlignedIndexCore j) ∧
      Real.log ((4 * (j + 1) : ℕ) : ℝ) *
          CPFormal.Carry.Cp.criticalAmplitude 2 (c2AlignedIndexDepth j) =
        Real.log 2 * ProjectiveDepth.newtonJet
            (CPFormal.Analytic.Cp.primeCarryAmplitudeRatio 2) 1
              (c2AlignedIndexDepth j) +
          primeDepthLogLedger (c2AlignedIndexCore j) *
            ProjectiveDepth.newtonJet
              (CPFormal.Analytic.Cp.primeCarryAmplitudeRatio 2) 0
                (c2AlignedIndexDepth j) := by
  refine ⟨c2AlignedCenter_eq_oddCoreCenter j,
    c2AlignedLeftLeg_eq_c2FiberPoint_minus j,
    c2AlignedRightLeg_eq_c2FiberPoint_plus j,
    c2LeftIncidence_effectiveDepth_eq_fiberDepth j,
    c2RightIncidence_effectiveDepth_eq_fiberDepth j,
    c2AlignedCenter_log_eq_currentDepth_add_primeCoreLedger j, ?_⟩
  rw [primeDepthLogLedger_eq_log
    (Nat.ne_of_gt (c2AlignedIndexCore_pos j))]
  exact c2AlignedCenter_log_amplitude_eq_green_and_seed j

/-! ## The finite native all-order readout -/

/-- The native Taylor readout of the finite C2 camera is exactly the seed plus
the fibre brackets.  No moment matrix or Jacobi operator occurs in this
identity. -/
theorem canonicalC2Geometry_nativeTaylorReadout_eq_seed_add_fibreBrackets
    (M order : ℕ) :
    evalFormalStencil
        (fun n => nativeDirichletSlopeTaylorCoefficient order n)
        (finiteStencil 2 M) =
      evalFormalStencil
          (fun n => nativeDirichletSlopeTaylorCoefficient order n)
          (seedStencil 2) +
        ∑ j ∈ Finset.range M,
          c2FiberNativeTaylorBracket order
            (c2AlignedIndexCore j) (c2AlignedIndexDepth j) :=
  c2FiniteCamera_nativeTaylorCoefficient_eq_seed_add_fiberBracketSum M order

/-- The corresponding logarithmic-power readout has the same native fibre
decomposition. -/
theorem canonicalC2Geometry_logPowerReadout_eq_seed_add_fibreBrackets
    (M order : ℕ) :
    evalFormalStencil
        (fun n => realLogPowerDirichletPower order (1 / 2 : ℂ) (n : ℝ))
        (finiteStencil 2 M) =
      evalFormalStencil
          (fun n => realLogPowerDirichletPower order (1 / 2 : ℂ) (n : ℝ))
          (seedStencil 2) +
        ∑ j ∈ Finset.range M,
          c2FiberAllOrderBracket order
            (c2AlignedIndexCore j) (c2AlignedIndexDepth j) :=
  c2FiniteCamera_allOrderLogPowerReadout_eq_seed_add_fiberBracketSum M order

/-! ## Exact downstream state identification -/

/-- Replacing the logarithm by the prime-depth ledger does not change the
completed TFVD Hilbert prefix: it is the same native state, now written in the
coordinates exposed by the C2 geometry. -/
theorem canonicalC2Geometry_primeDepthPrefix_eq_completedTfvd
    (M : ℕ) (time : ℝ) :
    finitePrimeDepthGeneratedC3HilbertPrefixState M time =
      canonicalCompletedC3HilbertPrefixState (nativeLine time) M :=
  finitePrimeDepthGeneratedC3HilbertPrefixState_eq_completedTfvd M time

end
end CarrySelfAdjointOperator
