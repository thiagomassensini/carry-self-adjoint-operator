import CarrySelfAdjointOperator.C2LiteralCameraAllOrderJetCrosswalk
import CarrySelfAdjointOperator.PrimeDepthTfvdLogJetCrosswalk
import CarrySelfAdjointOperator.CompletedNativeCameraUniversality
import CarrySelfAdjointOperator.CompletedNativeCorrectedCausalChiralGate
import CarrySelfAdjointOperator.CompletedNativeCorrectedClockBoundaryGate
import NativeCarrySpectralWeyl.Camera.BracketProfileBridge
import Mathlib.Algebra.Polynomial.Eval.Degree

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
open CPFormal.Analytic.Cp
open ProjectiveDepth
open FiniteNativeCarryOperator
open C3TraceDynamics
open NativeCarryC3Crosswalk
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

/-! ## Camera-factor removal and the common Green/chiral target -/

/-- The finite aligned C2 characteristic is exactly the periodic-profile
Dirichlet prefix described by the geometric pushforward. -/
theorem canonicalC2Geometry_finiteCharacteristic_eq_profilePrefix
    (cutoff : ℕ) (s : ℂ) :
    finiteBracketCharacteristic 2 cutoff s =
      coefficientDirichletPrefix c2Profile (4 * cutoff + 1) s :=
  finiteBracketCharacteristic_two_eq_profilePrefix cutoff s

/-- On the absolutely convergent half-plane, the C2 profile is the explicit
camera factor times the common positive Dirichlet series. -/
theorem canonicalC2Geometry_profileSeries_eq_factor_mul_positiveSeries
    {s : ℂ} (hs : 1 < s.re) :
    coefficientDirichletSeries c2Profile s =
      c2Factor s * positiveDirichletSeries s :=
  c2ProfileDirichletSeries_factorization hs

/-- After completion and exact division by the nonvanishing C2 factor, the
camera returns the common completed characteristic on the whole native line. -/
theorem canonicalC2Geometry_completedNormalizedCamera_eq_commonCharacteristic
    (cutoff : ℕ) :
    normalizedCompletedNativeCameraCharacteristic 2 cutoff =
      (fun time : ℝ =>
        completedNativeOperatorCharacteristic (time : ℂ)) := by
  exact normalizedCompletedNativeCameraCharacteristic_eq (by norm_num) cutoff

/-- The logarithmic moment sequence reconstructed from the normalized C2
camera is exactly the canonical native moment sequence. -/
theorem canonicalC2Geometry_cameraMoments_eq_canonical (cutoff : ℕ) :
    completedNativeCameraLogDerivativeMoment 2 cutoff =
      canonicalCompletedNativeLogDerivativeMoment := by
  exact completedNativeCameraLogDerivativeMoment_eq_canonical
    (by norm_num) cutoff

/-- The corrected Green/chiral boundary coefficient is the two-variable
polarized moment coefficient of the factor-cancelled C2 camera.  This is the
source-level handoff to the height gate; no Hankel or Jacobi object occurs. -/
theorem canonicalC2Geometry_correctedChiralCoefficient_eq_cameraMoments
    (M cutoff p q : ℕ) :
    canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M (p + q) =
      polarizedGreenMomentCoefficient
        (completedNativeCameraLogDerivativeMoment 2 cutoff) p q := by
  rw [canonicalC2Geometry_cameraMoments_eq_canonical cutoff]
  exact canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_polarizedMoment
    M p q

/-! ## Exact finite-head / tail sewing -/

/-- The C2 finite head plus its exact omitted-center tail is the native scalar
    dressed by the C2 camera factor.  This is the discrete completion identity
    before normalization and before any moment or Gram construction. -/
theorem canonicalC2Geometry_finiteHead_add_exactTail_eq_factor_mul_nativeScalar
    (cutoff : ℕ) {s : ℂ} (hs : s ∈ nativeScalarDomain) :
    finiteBracketCharacteristic 2 cutoff s +
        (∑' index : ℕ, centerBracketTerm 2 s (index + cutoff)) =
      factor 2 s * nativeScalar s := by
  exact complete_head_add_complete_center_tail_eq_factor_mul_nativeScalar
    (camera := 2) (cutoff := cutoff) (by norm_num) hs

/-- The packaged all-order native jet is literally the C2 finite head plus the
    exact center tail, after taking the real native-line derivative. -/
theorem canonicalC2Geometry_completedPackagedNativeJet_eq_head_add_exactTail
    (cutoff order : ℕ) (time : ℝ) :
    completedPackagedFiniteNativeOperatorJet 2 cutoff order time =
      iteratedDeriv order
        (fun u : ℝ ↦
          finiteBracketCharacteristic 2 cutoff (nativeLine u) +
            ∑' index : ℕ, centerBracketTerm 2 (nativeLine u) (index + cutoff))
        time := by
  have hfun :
      (fun u : ℝ ↦
          finiteBracketCharacteristic 2 cutoff (nativeLine u) +
            ∑' index : ℕ, centerBracketTerm 2 (nativeLine u) (index + cutoff)) =
        (fun u : ℝ ↦ completedNativeCharacteristic 2 cutoff (nativeLine u)) := by
    funext u
    rfl
  rw [hfun]
  exact completedPackagedFiniteNativeOperatorJet_eq_completedNativeCharacteristic
    (camera := 2) (by norm_num) cutoff order time

/-- At order zero, exact head--tail completion followed by C2-factor removal
    lands directly on the common completed native characteristic. -/
theorem canonicalC2Geometry_completedPackagedNativeJet_zero_normalized_eq_commonCharacteristic
    (cutoff : ℕ) (time : ℝ) :
    nativeXiCompletionFactor (time : ℂ) *
        completedPackagedFiniteNativeOperatorJet 2 cutoff 0 time /
          factor 2 (nativeLine time) =
      completedNativeOperatorCharacteristic (time : ℂ) := by
  have hpack :
      completedPackagedFiniteNativeOperatorJet 2 cutoff 0 time =
        completedNativeCharacteristic 2 cutoff (nativeLine time) := by
    simpa only [iteratedDeriv_zero] using
      (completedPackagedFiniteNativeOperatorJet_eq_completedNativeCharacteristic
        (camera := 2) (by norm_num) cutoff 0 time)
  have hnorm :=
    congrFun (canonicalC2Geometry_completedNormalizedCamera_eq_commonCharacteristic
      cutoff) time
  simpa [normalizedCompletedNativeCameraCharacteristic, hpack] using hnorm

/-! ## Coefficient-level packaging and rotation -/

/-- The finite C2 native jet, before exact completion, is the complex
    finite-characteristic jet with precisely the native-line rotation
    `I^order`.  This is the real-to-complex packaging seam; it is not a Gram
    construction. -/
theorem canonicalC2Geometry_packagedFiniteNativeOperatorJet_eq_complex
    (cutoff order : ℕ) (time : ℝ) :
    nativeCarryRealPlaneComplexPackaging
        (iteratedDeriv order
          (fun u : ℝ => Operator.finiteNativeOperator 2 cutoff u) time) =
      iteratedDeriv order
          (finiteBracketCharacteristic 2 cutoff) (nativeLine time) *
        Complex.I ^ order := by
  exact packaged_iteratedDeriv_finiteNativeOperator_eq_complex
    (camera := 2) (by norm_num) cutoff order time

/-- After exact C2 factor removal, every real native-line derivative is the
    derivative of the same completed characteristic.  This keeps the
    normalized scalar readout distinct from the unnormalized finite jet above. -/
theorem canonicalC2Geometry_normalizedCamera_iteratedDeriv_eq_common
    (cutoff order : ℕ) (time : ℝ) :
    iteratedDeriv order
        (normalizedCompletedNativeCameraCharacteristic 2 cutoff) time =
      iteratedDeriv order completedNativeOperatorCharacteristic
        (time : ℂ) := by
  exact iteratedDeriv_normalizedCompletedNativeCameraCharacteristic
    (by norm_num) cutoff order time

/-- The corrected native chiral readout has the C2 camera moments as its odd
    Taylor coefficients.  This is the coefficient-level handoff from the
    normalized geometric camera to the polarized Green moment kernel. -/
theorem canonicalC2Geometry_correctedChiralCoefficient_odd_eq_cameraMoment
    (M cutoff n : ℕ) :
    canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M (2 * n) =
      (completedNativeCameraLogDerivativeMoment 2 cutoff n : ℂ) := by
  rw [canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_odd_eq_canonicalMoment]
  rw [canonicalC2Geometry_cameraMoments_eq_canonical cutoff]

/-! ## C2 specialization of the two-variable transport gate -/

/-- If a seeded material atlas realizes the corrected native C2 boundary
    column, then that column is already the C2 factor-cancelled polarized
    Green column.  The statement is coefficient-level and does not introduce
    a Gram or Jacobi construction. -/
theorem canonicalC2Geometry_seededClockFirstColumn_eq_cameraPolarizedMoment
    {ι : Type*} [Fintype ι]
    (M cutoff : ℕ) (block : ι → SeededClockBlock) (p : ℕ)
    (htransport : HasCorrectedNativeSeededClockBoundaryTransport M block) :
    seededClockAtlasCoefficient block p 0 =
      polarizedGreenMomentCoefficient
        (completedNativeCameraLogDerivativeMoment 2 cutoff) p 0 := by
  calc
    seededClockAtlasCoefficient block p 0 =
        canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p :=
      htransport p
    _ = polarizedGreenMomentCoefficient
        (completedNativeCameraLogDerivativeMoment 2 cutoff) p 0 := by
      rw [canonicalC2Geometry_cameraMoments_eq_canonical cutoff]
      exact canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_polarizedMoment
        M p 0

/-- The corrected C2 boundary transport is sufficient to close the complete
    two-variable Green moment kernel of the seeded-clock parity jet.  The
    only unproved input is the material first-column calibration itself; the
    interior transport is inherited from the exact seeded-clock shift. -/
theorem canonicalC2Geometry_seededClockGreenMomentKernel_of_correctedTransport
    {ι : Type*} [Fintype ι]
    (M cutoff : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeSeededClockBoundaryTransport M block) :
    IsComplexGreenWronskianMomentKernelGramRepresentation
      (completedNativeCameraLogDerivativeMoment 2 cutoff)
      (polarizedCoefficientParityJet (seededClockAtlasJet block)) := by
  rw [canonicalC2Geometry_cameraMoments_eq_canonical cutoff]
  exact seededClockAtlasGreenMomentKernel_of_correctedNativeChiralBoundaryTransport
    M block htransport

/-! ## The remaining material equation in explicit atomic form -/

/-- Every material-clock coefficient is a finite four-atom power sum.  This
    is an expansion of the existing reconstructed clock, not a new spectral
    carrier: the four atoms are exactly its nodal frequencies and the weights
    are the squared nodal seed amplitudes. -/
theorem canonicalC2Geometry_seededClockCoefficient_eq_fourAtomPowerSum
    (d a b c : ℝ) (x : SeededC3Data) (p q : ℕ) :
    seededClockMaterialCoefficient d a b c x p q =
      ∑ i : Fin 4,
        (starRingEnd ℂ) (seededRecover x i) * seededRecover x i *
          (((![d, a, b, c] i : ℝ) : ℂ) ^ (p + q)) := by
  simpa [seededClockMaterialCoefficient, seededClockMaterialRawJet] using
    (inner_seededRecover_clock_iterate d a b c x x p q)

/-- The finite orthogonal material atlas is therefore a finite sum of the
    preceding four-atom power sums. -/
theorem canonicalC2Geometry_seededClockAtlasCoefficient_eq_finiteAtomicPowerSum
    {ι : Type*} [Fintype ι]
    (block : ι → SeededClockBlock) (p q : ℕ) :
    seededClockAtlasCoefficient block p q =
      ∑ k : ι, ∑ i : Fin 4,
        (starRingEnd ℂ) (seededRecover (block k).state i) *
          seededRecover (block k).state i *
            (((![ (block k).d, (block k).a, (block k).b, (block k).c ] i : ℝ) : ℂ) ^
              (p + q)) := by
  unfold seededClockAtlasCoefficient
  apply Finset.sum_congr rfl
  intro k hk
  exact canonicalC2Geometry_seededClockCoefficient_eq_fourAtomPowerSum
    (block k).d (block k).a (block k).b (block k).c (block k).state p q

/-- Named residual for the still-open first-column calibration. -/
def canonicalC2Geometry_seededClockBoundaryResidual
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock) (p : ℕ) : ℂ :=
  seededClockAtlasCoefficient block p 0 -
    canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p

/-- Vanishing of the named residual is exactly the corrected-native boundary
    transport hypothesis. -/
theorem canonicalC2Geometry_seededClockBoundaryResidual_zero_iff_correctedTransport
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock) :
    (∀ p : ℕ,
      canonicalC2Geometry_seededClockBoundaryResidual M block p = 0) ↔
      HasCorrectedNativeSeededClockBoundaryTransport M block := by
  constructor
  · intro h p
    exact sub_eq_zero.mp (h p)
  · intro h p
    exact sub_eq_zero.mpr (h p)

/-- The residual is exactly the finite atomic power sum minus the C2
    factor-cancelled polarized Green target.  This is the concrete equation
    that a genuine material atlas must solve. -/
theorem canonicalC2Geometry_seededClockBoundaryResidual_eq_atomicPowerSum_sub_cameraTarget
    {ι : Type*} [Fintype ι]
    (M cutoff : ℕ) (block : ι → SeededClockBlock) (p : ℕ) :
    canonicalC2Geometry_seededClockBoundaryResidual M block p =
      (∑ k : ι, ∑ i : Fin 4,
        (starRingEnd ℂ) (seededRecover (block k).state i) *
          seededRecover (block k).state i *
            (((![ (block k).d, (block k).a, (block k).b, (block k).c ] i : ℝ) : ℂ) ^ p)) -
        polarizedGreenMomentCoefficient
          (completedNativeCameraLogDerivativeMoment 2 cutoff) p 0 := by
  unfold canonicalC2Geometry_seededClockBoundaryResidual
  rw [canonicalC2Geometry_seededClockAtlasCoefficient_eq_finiteAtomicPowerSum]
  simp only [Nat.add_zero]
  have htarget :
      canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p =
        polarizedGreenMomentCoefficient
          (completedNativeCameraLogDerivativeMoment 2 cutoff) p 0 := by
    simpa only [Nat.add_zero] using
      (canonicalC2Geometry_correctedChiralCoefficient_eq_cameraMoments
        M cutoff p 0)
  rw [htarget]

/-! ## The finite atomic recurrence forced by the native clock -/

/-- Characteristic polynomial of the four nodal frequencies of one material
    clock block.  This is a diagnostic polynomial for the material carrier;
    it does not define the Green or height operator. -/
def canonicalC2Geometry_seededClockBlockCharacteristic
    (block : SeededClockBlock) : Polynomial ℂ :=
  ∏ i : Fin 4,
    (Polynomial.X - Polynomial.C
      (((![block.d, block.a, block.b, block.c] i : ℝ) : ℂ)))

/-- Every native nodal frequency is a root of its block characteristic. -/
theorem canonicalC2Geometry_seededClockBlockCharacteristic_root
    (block : SeededClockBlock) (i : Fin 4) :
    (canonicalC2Geometry_seededClockBlockCharacteristic block).eval
        (((![block.d, block.a, block.b, block.c] i : ℝ) : ℂ)) = 0 := by
  unfold canonicalC2Geometry_seededClockBlockCharacteristic
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

/-- Product characteristic of a finite atlas.  It annihilates every atom of
    every block, hence every finite atomic boundary sequence. -/
def canonicalC2Geometry_seededClockAtlasCharacteristic
    {ι : Type*} [Fintype ι]
    (block : ι → SeededClockBlock) : Polynomial ℂ :=
  ∏ k : ι, canonicalC2Geometry_seededClockBlockCharacteristic (block k)

/-- Every atom in a finite atlas is a root of the atlas characteristic. -/
theorem canonicalC2Geometry_seededClockAtlasCharacteristic_root
    {ι : Type*} [Fintype ι]
    (block : ι → SeededClockBlock) (k : ι) (i : Fin 4) :
    (canonicalC2Geometry_seededClockAtlasCharacteristic block).eval
        (((![(block k).d, (block k).a, (block k).b, (block k).c] i : ℝ) : ℂ)) = 0 := by
  unfold canonicalC2Geometry_seededClockAtlasCharacteristic
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  exact canonicalC2Geometry_seededClockBlockCharacteristic_root (block k) i

/-- Every finite seeded-clock atlas satisfies an exact scalar linear recurrence.
    This is a necessary consequence of the native four-corner clock and is
    independent of Hankel, Cholesky, Jacobi, or any fitted normalization. -/
theorem canonicalC2Geometry_seededClockAtlasCoefficient_recurrence
    {ι : Type*} [Fintype ι]
    (block : ι → SeededClockBlock) (n : ℕ) :
    ∑ r ∈ Finset.range
        ((canonicalC2Geometry_seededClockAtlasCharacteristic block).natDegree + 1),
      (canonicalC2Geometry_seededClockAtlasCharacteristic block).coeff r *
        seededClockAtlasCoefficient block (n + r) 0 = 0 := by
  simp_rw [canonicalC2Geometry_seededClockAtlasCoefficient_eq_finiteAtomicPowerSum]
  simp only [Nat.add_zero]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  calc
    (∑ x ∈ Finset.range
        ((canonicalC2Geometry_seededClockAtlasCharacteristic block).natDegree + 1),
        (canonicalC2Geometry_seededClockAtlasCharacteristic block).coeff x *
          ((starRingEnd ℂ) (seededRecover (block k).state i) *
            seededRecover (block k).state i *
              (((![(block k).d, (block k).a, (block k).b, (block k).c] i : ℝ) : ℂ) ^
                (n + x)))) =
      (starRingEnd ℂ) (seededRecover (block k).state i) *
        seededRecover (block k).state i *
          (((![(block k).d, (block k).a, (block k).b, (block k).c] i : ℝ) : ℂ) ^ n) *
            (∑ x ∈ Finset.range
                ((canonicalC2Geometry_seededClockAtlasCharacteristic block).natDegree + 1),
              (canonicalC2Geometry_seededClockAtlasCharacteristic block).coeff x *
                (((![(block k).d, (block k).a, (block k).b, (block k).c] i : ℝ) : ℂ) ^ x)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [pow_add]
        ring
    _ = 0 := by
      rw [← Polynomial.eval_eq_sum_range]
      rw [canonicalC2Geometry_seededClockAtlasCharacteristic_root]
      ring

/-- If the corrected material transport actually closes, then the C2
    polarized Green boundary sequence must satisfy the same finite recurrence.
    This is the first exact obstruction/test for a proposed finite atlas. -/
theorem canonicalC2Geometry_seededClockAtlas_target_recurrence
    {ι : Type*} [Fintype ι]
    (M cutoff : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeSeededClockBoundaryTransport M block) (n : ℕ) :
    ∑ r ∈ Finset.range
        ((canonicalC2Geometry_seededClockAtlasCharacteristic block).natDegree + 1),
      (canonicalC2Geometry_seededClockAtlasCharacteristic block).coeff r *
        polarizedGreenMomentCoefficient
          (completedNativeCameraLogDerivativeMoment 2 cutoff) (n + r) 0 = 0 := by
  have hrec := canonicalC2Geometry_seededClockAtlasCoefficient_recurrence block n
  simpa only [canonicalC2Geometry_seededClockFirstColumn_eq_cameraPolarizedMoment
    M cutoff block _ htransport] using hrec

/-- The same necessary recurrence written directly for the canonical native
    moment sequence, using camera universality only after the material-to-C2
    transport has been assumed. -/
theorem canonicalC2Geometry_seededClockAtlas_canonicalTarget_recurrence
    {ι : Type*} [Fintype ι]
    (M cutoff : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeSeededClockBoundaryTransport M block) (n : ℕ) :
    ∑ r ∈ Finset.range
        ((canonicalC2Geometry_seededClockAtlasCharacteristic block).natDegree + 1),
      (canonicalC2Geometry_seededClockAtlasCharacteristic block).coeff r *
        polarizedGreenMomentCoefficient
          canonicalCompletedNativeLogDerivativeMoment (n + r) 0 = 0 := by
  have hrec := canonicalC2Geometry_seededClockAtlas_target_recurrence
    M cutoff block htransport n
  simpa only [completedNativeCameraLogDerivativeMoment_eq_canonical
    (camera := 2) (by norm_num) cutoff] using hrec

end
end CarrySelfAdjointOperator
