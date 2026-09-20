import CarrySelfAdjointOperator.CompletedNativeCorrectedChiralClockMomentKernel
import CarrySelfAdjointOperator.CompletedNativeChiralBlockMomentProbe
import CarrySelfAdjointOperator.CompletedNativeSeededClockAtomicGate
import CarrySelfAdjointOperator.DiscreteProjectiveReconstruction
import CarrySelfAdjointOperator.NativeMomentProjectiveValveBridge
import CarrySelfAdjointOperator.CompletedNativeC2HaarDoubleLog4Transport
import CPFormal.Analytic.CpUniversalCarryStructuralPersistence
import Mathlib.Tactic

/-!
# Native first/second-layer audit

This module records the coefficient genealogy that is already native to the
completed construction.  It intentionally does **not** introduce a positive
carrier, a new Gram realization, a dilation, or an assumption of Hankel/Pick
positivity.

There are three distinct statements which must not be conflated:

* the corrected clock coefficient has an exact parity split into the ordinary
  and shifted Hankel arrays;
* the complete Wronskian has genuinely orthogonal positive/negative *chiral*
  channels, but the scalar moment readout is their signed difference;
* the projective reconstruction keeps value and slope before its
  `X^2`-weighted bracket/curvature channel.

Consequently the first remaining material sewing gate is the all-order
first-column calibration of a concrete seeded clock.  The one-block atlas
already fails this gate at coefficient `(0,0)`.

The C2/Haar portion is deliberately limited to the upstream coding identity
and the existing readout-atlas ledger invariant.  Neither is a claim that C2
is a geometric C4, nor a matched-horizon metric/POVM transport.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace Matrix

namespace CarrySelfAdjointOperator

open PowerSeries
open C3TraceDynamics

noncomputable section

/-- The requested low-order permutation: it visits the corrected-clock orders
`0, 2, 1, 3`, so its first two coordinates are even and its last two are odd.
This is an indexing device only; it does not change a metric. -/
def canonicalCompletedNativeClockN2ParityOrder (i : Fin 4) : ℕ :=
  ![0, 2, 1, 3] i

@[simp] theorem canonicalCompletedNativeClockN2ParityOrder_values :
    (canonicalCompletedNativeClockN2ParityOrder 0,
      canonicalCompletedNativeClockN2ParityOrder 1,
      canonicalCompletedNativeClockN2ParityOrder 2,
      canonicalCompletedNativeClockN2ParityOrder 3) =
      (0, 2, 1, 3) := by
  simp [canonicalCompletedNativeClockN2ParityOrder]

/-- The raw order-`0,1,2,3` corrected-clock coefficient matrix. -/
def canonicalCompletedNativeClockN2RawMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(canonicalCompletedNativeCorrectedClockTowerCoefficient 0 0),
      (canonicalCompletedNativeCorrectedClockTowerCoefficient 0 1),
      (canonicalCompletedNativeCorrectedClockTowerCoefficient 0 2),
      (canonicalCompletedNativeCorrectedClockTowerCoefficient 0 3);
     (canonicalCompletedNativeCorrectedClockTowerCoefficient 1 0),
      (canonicalCompletedNativeCorrectedClockTowerCoefficient 1 1),
      (canonicalCompletedNativeCorrectedClockTowerCoefficient 1 2),
      (canonicalCompletedNativeCorrectedClockTowerCoefficient 1 3);
     (canonicalCompletedNativeCorrectedClockTowerCoefficient 2 0),
      (canonicalCompletedNativeCorrectedClockTowerCoefficient 2 1),
      (canonicalCompletedNativeCorrectedClockTowerCoefficient 2 2),
      (canonicalCompletedNativeCorrectedClockTowerCoefficient 2 3);
     (canonicalCompletedNativeCorrectedClockTowerCoefficient 3 0),
      (canonicalCompletedNativeCorrectedClockTowerCoefficient 3 1),
      (canonicalCompletedNativeCorrectedClockTowerCoefficient 3 2),
      (canonicalCompletedNativeCorrectedClockTowerCoefficient 3 3)]

/-- The raw low-order coefficient table.  This is the formal version of
`[[h₀,0,h₁,0],[0,h₁,0,h₂],[h₁,0,h₂,0],[0,h₂,0,h₃]]`. -/
theorem canonicalCompletedNativeClockN2RawMatrix_eq :
    canonicalCompletedNativeClockN2RawMatrix =
      !![(canonicalCompletedNativeLogDerivativeMoment 0 : ℂ), 0,
          (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ), 0;
         0, (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ), 0,
          (canonicalCompletedNativeLogDerivativeMoment 2 : ℂ);
         (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ), 0,
          (canonicalCompletedNativeLogDerivativeMoment 2 : ℂ), 0;
         0, (canonicalCompletedNativeLogDerivativeMoment 2 : ℂ), 0,
          (canonicalCompletedNativeLogDerivativeMoment 3 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [canonicalCompletedNativeClockN2RawMatrix,
      canonicalCompletedNativeCorrectedClockTowerCoefficient,
      polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient]

/-- Reindexing the preceding table by `0,2,1,3` produces the two requested
low-order blocks.  The upper-left block is `G₂`; the lower-right block is
`K₂`, with the first shift appearing at its `(0,0)` entry `h₁`. -/
theorem canonicalCompletedNativeClockN2ParityBlock_eq :
    (fun i j : Fin 4 =>
      canonicalCompletedNativeCorrectedClockTowerCoefficient
        (canonicalCompletedNativeClockN2ParityOrder i)
        (canonicalCompletedNativeClockN2ParityOrder j)) =
      !![(canonicalCompletedNativeLogDerivativeMoment 0 : ℂ),
          (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ), 0, 0;
         (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ),
          (canonicalCompletedNativeLogDerivativeMoment 2 : ℂ), 0, 0;
         0, 0, (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ),
          (canonicalCompletedNativeLogDerivativeMoment 2 : ℂ);
         0, 0, (canonicalCompletedNativeLogDerivativeMoment 2 : ℂ),
          (canonicalCompletedNativeLogDerivativeMoment 3 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [canonicalCompletedNativeClockN2ParityOrder,
      canonicalCompletedNativeCorrectedClockTowerCoefficient,
      polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient]

/-- The two blocks in the previous theorem are literally the ordinary and
shifted `2 × 2` Hankel arrays, after scalar extension to `ℂ`. -/
def correctedClockN2ParityIndex : Fin 2 ⊕ Fin 2 → ℕ
  | Sum.inl i => 2 * (i : ℕ)
  | Sum.inr i => 2 * (i : ℕ) + 1

theorem canonicalCompletedNativeClockN2ParityBlock_eq_hankelBlocks
    (i j : Fin 2 ⊕ Fin 2) :
    canonicalCompletedNativeCorrectedClockTowerCoefficient
        (correctedClockN2ParityIndex i)
        (correctedClockN2ParityIndex j) =
      match i, j with
      | Sum.inl i, Sum.inl j =>
          (canonicalCompletedNativeLogDerivativeMoment ((i : ℕ) + (j : ℕ)) : ℂ)
      | Sum.inr i, Sum.inr j =>
          (canonicalCompletedNativeLogDerivativeMoment ((i : ℕ) + (j : ℕ) + 1) : ℂ)
      | Sum.inl _, Sum.inr _ => 0
      | Sum.inr _, Sum.inl _ => 0 := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp [correctedClockN2ParityIndex,
      canonicalCompletedNativeCorrectedClockTowerCoefficient]

/-- The even corner of the parity-ordered microscope is literally the
ordinary Hankel matrix `G₂`, after scalar extension. -/
theorem canonicalCompletedNativeClockN2_evenBlock_eq_hankelGram
    (i j : Fin 2) :
    canonicalCompletedNativeCorrectedClockTowerCoefficient
        (correctedClockN2ParityIndex (Sum.inl i))
        (correctedClockN2ParityIndex (Sum.inl j)) =
      ((hankelGram canonicalCompletedNativeLogDerivativeMoment 2 i j : ℝ) : ℂ) := by
  simp [correctedClockN2ParityIndex,
    canonicalCompletedNativeCorrectedClockTowerCoefficient]

/-- The odd corner of the same microscope is literally the shifted Hankel
matrix `K₂`, after scalar extension. -/
theorem canonicalCompletedNativeClockN2_oddBlock_eq_shiftedHankel
    (i j : Fin 2) :
    canonicalCompletedNativeCorrectedClockTowerCoefficient
        (correctedClockN2ParityIndex (Sum.inr i))
        (correctedClockN2ParityIndex (Sum.inr j)) =
      ((shiftedHankel canonicalCompletedNativeLogDerivativeMoment 2 i j : ℝ) : ℂ) := by
  simp [correctedClockN2ParityIndex,
    canonicalCompletedNativeCorrectedClockTowerCoefficient]

/-- The two parity blocks have no mixed coefficient.  This is coefficient
orthogonality in the corrected tower; a material Hilbert realization still
requires the separate first-column/Green sewing gate recorded below. -/
theorem canonicalCompletedNativeClockN2_even_odd_coeff_zero
    (i j : Fin 2) :
    canonicalCompletedNativeCorrectedClockTowerCoefficient
        (correctedClockN2ParityIndex (Sum.inl i))
        (correctedClockN2ParityIndex (Sum.inr j)) = 0 := by
  simp [correctedClockN2ParityIndex,
    canonicalCompletedNativeCorrectedClockTowerCoefficient]

/-- The exact native source of every coefficient in the corrected tower is
the odd Taylor coefficient of the signed chiral block readout.  In
particular, this records `h₀,h₁,h₂,h₃` at orders `1,3,5,7`; it is not a
second-difference energy calibration. -/
theorem canonicalCompletedNativeChiralSignature_first_four_odd_variations
    (M : ℕ) :
    canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M 1 =
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) ∧
      canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M 3 =
        (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) ∧
      canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M 5 =
        (canonicalCompletedNativeLogDerivativeMoment 2 : ℂ) ∧
      canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M 7 =
        (canonicalCompletedNativeLogDerivativeMoment 3 : ℂ) := by
  refine ⟨canonicalCompletedC3ChiralBlockSignature_firstVariation_eq_moment_zero M,
    canonicalCompletedC3ChiralBlockSignature_thirdVariation_eq_moment_one M, ?_, ?_⟩
  · simpa using canonicalCompletedC3ChiralBlockSignature_odd_eq_canonicalMoment M 2
  · simpa using canonicalCompletedC3ChiralBlockSignature_odd_eq_canonicalMoment M 3

/-- Genuine Hilbert orthogonality found upstream.  Its indices are the
positive/negative *chiral* channels; it is not yet the even/odd clock-jet
orthogonality required for an unconditional Hankel Gram realization. -/
theorem canonicalCompletedNativeChiralChannels_orthogonal
    (M : ℕ) (w z : ℂ) :
    inner ℂ
      (canonicalCompletedC3NormalizedFullWronskianChiralState M
        .positive w)
      (canonicalCompletedC3NormalizedFullWronskianChiralState M
        .negative z) = 0 := by
  exact canonicalCompletedC3NormalizedFullWronskianChiralBlockKernel_positive_negative M w z

/-- The same scalar readout is explicitly a signed positive-minus-negative
chiral diagonal, which prevents promoting the preceding orthogonality to a
moment Gram theorem without an additional material polarization bridge. -/
theorem canonicalCompletedNativeMomentReadout_is_signedChiralReadout
    (M : ℕ) (z : ℂ) :
    canonicalCompletedC3FullWronskianChiralBalanceResponse M z =
      Complex.I * canonicalCompletedC3ChiralSignatureReadout
        (canonicalCompletedC3NormalizedFullWronskianChiralBlockKernel M 0 z) :=
  canonicalCompletedC3FullWronskianChiralBalanceResponse_eq_blockSignature M z

/-- Projective reconstruction has its affine boundary/value and slope terms
before the `X^2` Green-curvature term.  Thus the raw bracket is not a valid
candidate for the zeroth moment merely by order bookkeeping. -/
theorem discreteProjective_reconstruct_affine_then_curvature
    {K : Type*} [Field K]
    (data : DiscreteProjective.ReconstructionData K) :
    mk (DiscreteProjective.reconstruct data) =
      C data.initialValue * DiscreteValve.geometricSeries +
        X * C data.initialSlope * DiscreteValve.greenKernelSeries +
        X ^ 2 * DiscreteValve.greenKernelSeries *
          ProjectiveDepth.fromProjective
            (ProjectiveValve.projectiveValveCurvature data.mass.1) :=
  DiscreteProjective.mk_reconstruct_eq_green data

/-- The graded valve channel `B = X Q`, where `Q` is the native log-derivative
moment series.  This is a series-level bookkeeping alias, not a new carrier.
It places `h₀` at first graded order and shifts `hₙ` to coefficient `n+1`. -/
def canonicalCompletedNativeValveGradedChannel : PowerSeries ℝ :=
  X * mk canonicalCompletedNativeLogDerivativeMoment

@[simp] theorem canonicalCompletedNativeValveGradedChannel_zero :
    coeff 0 canonicalCompletedNativeValveGradedChannel = 0 := by
  simp [canonicalCompletedNativeValveGradedChannel]

@[simp] theorem canonicalCompletedNativeValveGradedChannel_succ (n : ℕ) :
    coeff (n + 1) canonicalCompletedNativeValveGradedChannel =
      canonicalCompletedNativeLogDerivativeMoment n := by
  simp [canonicalCompletedNativeValveGradedChannel, PowerSeries.coeff_succ_X_mul]

/-- The scalar projective-valve normalization is exact: curvature of the
reciprocal normalized characteristic is the native moment series.  This does
not assert any Hilbert Gram or energy identity. -/
theorem canonicalCompletedNativeProjectiveValve_curvature_eq_moments :
    ProjectiveValve.projectiveValveCurvature
        normalizedCompletedNativeEvenFormalSeries⁻¹ =
      mk canonicalCompletedNativeLogDerivativeMoment :=
  projectiveValveCurvature_nativeReciprocal_eq_moments

/-- The first material obstruction is already coefficient `(0,0)` for the
literal one-block seeded-clock atlas.  The displayed quantity is its exact
central calibration residual. -/
def nativeZeroSeededClockCentralCalibrationResidual (s : ℂ) : ℝ :=
  ‖seededRecover (nativeBlockSeededData 0 s)‖ ^ 2 -
    canonicalCompletedNativeLogDerivativeMoment 0

theorem nativeZeroSeededClockCentralCalibrationResidual_ne_zero (s : ℂ) :
    nativeZeroSeededClockCentralCalibrationResidual s ≠ 0 := by
  unfold nativeZeroSeededClockCentralCalibrationResidual
  apply sub_ne_zero.mpr
  exact nativeBlockSeededData_zero_energy_ne_nativeMoment s

/-- Equivalently, the raw native one-block clock cannot satisfy the all-order
same-edge first-column transport.  This is a no-go only for that literal
atlas, not for a future geometrically supplied material polarization. -/
theorem nativeZeroSeededClock_firstColumn_gate_fails (M : ℕ) (s : ℂ) :
    ¬ HasSameEdgeGreenToClockBoundaryTransport M
        (fun _ : Fin 1 => nativeZeroSeededClockBlock s) :=
  nativeZeroSeededClockBlock_not_sameEdgeTransport M s

/-- The precise remaining material condition is the existing first-column
transport, not a positivity axiom. -/
theorem seededClock_correctedBoundaryTransport_iff_sameEdge
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock) :
    HasCorrectedNativeChiralBoundaryTransport M
        (seededClockAtlasCoefficient block) ↔
      HasSameEdgeGreenToClockBoundaryTransport M block :=
  seededClockAtlas_hasCorrectedNativeChiralBoundaryTransport_iff_sameEdgeTransport
    M block

/-- `primos` supplies the upstream coding fact used by the C2/Haar audit:
the aligned C2 scanner is the width-four, radius-one native scanner.  This
remains a coding identity and does not identify geometric C2 with C4. -/
theorem c2Haar_alignedC2_is_widthFour_radiusOne
    (M : ℕ) (f : ℤ → ℝ) :
    CPFormal.Analytic.Cp.nativeCarryAlignedC2Chart M f =
      CPFormal.Analytic.Cp.nativeCarryFiniteSaturatedChart 4 M f ∧
      CPFormal.Genuine.Cp.halfRange 4 = 1 :=
  nativeCarryC2_is_width_four_not_geometricC4 M f

/-- The same upstream readout-atlas infrastructure transports only the total
Green ledger.  It is therefore sufficient for the coding/readout audit, but
does not supply the missing componentwise or inner-product C2/Haar sewing. -/
theorem baseCarryGreen_totalLedger_invariant_audit
    (source target : CPFormal.Analytic.Cp.CarryMaterialBase)
    (x : CPFormal.Analytic.Cp.CarryVerticalL2) :
    (CPFormal.Analytic.Cp.baseCarryGreenReadoutAtlas.interior target
          (CPFormal.Analytic.Cp.baseCarryGreenReadoutAtlas.transport source target x) +
        CPFormal.Analytic.Cp.baseCarryGreenReadoutAtlas.boundary target
          (CPFormal.Analytic.Cp.baseCarryGreenReadoutAtlas.transport source target x)) =
      CPFormal.Analytic.Cp.baseCarryGreenReadoutAtlas.interior source x +
        CPFormal.Analytic.Cp.baseCarryGreenReadoutAtlas.boundary source x :=
  CPFormal.Analytic.Cp.baseCarryGreen_totalLedger_invariant source target x

end

end CarrySelfAdjointOperator
