import CarrySelfAdjointOperator.ProjectiveValveCarryEnergyFrontier
import CarrySelfAdjointOperator.NativeLogEvolution
import CarrySelfAdjointOperator.CompletedNativeCharacteristic
import CarrySelfAdjointOperator.CompletedNativeGeometryHeightProvenance
import CarrySelfAdjointOperator.UnconditionalLimitConfinementProbe

/-!
# Minimal native-carry representation capstone

This file deliberately compresses the unconditional part of the native-carry
architecture.  `NativeCarryRepresentationCore` has five fields only:

1. positional carry mass is the square of the canonical amplitude;
2. TFVD Green-plus-return reconstruction is exact;
3. the native logarithmic clock is self-adjoint;
4. that clock has the literal `log (n + 1)` basis law;
5. every supported completed camera characteristic is the same native scalar,
   up to its explicit camera factor.

The four-channel energy formula is a polarization of field 2, while completed
moments, Jacobi sections, and finite height operators are downstream readouts.
The C3 zero-confinement statement is intentionally *not* a field: its exact
remaining scalarization seam is displayed as a separate conditional frontier.
In particular, no Green-port presentation, radial normalization, six-source
implementation, or historical carrier is part of this core.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera
open FiniteNativeCarryOperator.Camera

noncomputable section

/-- The irreducible unconditional representation data of native carry geometry.

This is a proposition packaging already-formalized theorems; it introduces no
new mathematical construction.  The generic TFVD identity is deliberately
kept separate from its positional specialization: the first says that analysis
and synthesis reconstruct exactly, while the first field says which ratio is
selected by carry geometry. -/
structure NativeCarryRepresentationCore : Prop where
  /-- The positional amplitude used by the geometry has exactly the carry mass
  as its quadratic weight. -/
  positionalMass :
    ∀ base k : ℕ,
      (canonicalBR2CarryAmplitudeRatio base ^ k) ^ 2 =
        CarryGeometry.carryMass base k
  /-- Exact TFVD reconstruction: centered bracket data plus boundary trace
  reconstruct every vertical Hilbert state. -/
  tfvdReconstruction :
    ∀ (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1),
      carryVerticalL2WeightedGreen q ∘L
            carryWeightedVerticalCenteredBracket q +
          carryWeightedVerticalReturn q hqpos.le hq1 ∘L
            carryWeightedVerticalTrace q =
        ContinuousLinearMap.id ℂ CarryVerticalL2
  /-- The clock driving the native evolution is self-adjoint on its maximal
  domain. -/
  logClockSelfAdjoint : IsSelfAdjoint nativeLogGenerator
  /-- In the canonical basis the clock is literally multiplication by
  `log (n + 1)`. -/
  logClockBasisLaw :
    ∀ n : ℕ,
      nativeLogGenerator
          ⟨infiniteRealSpectralBasisVector n,
            nativeLogBasisVector_mem_domain n⟩ =
        (Real.log (((n + 1 : ℕ) : ℝ)) : ℂ) •
          infiniteRealSpectralBasisVector n
  /-- A completed camera is only a presentation of the common native scalar;
  its camera-dependent factor remains explicit. -/
  commonNativeCharacteristic :
    ∀ {camera cutoff : ℕ} (_hcamera : 2 ≤ camera) {s : ℂ},
      s ∈ nativeScalarDomain →
        completedNativeCharacteristic camera cutoff s =
          factor camera s * nativeScalar s

/-- The minimal native-carry representation is closed unconditionally.

Its proof is intentionally just the five pre-existing capstones named by the
fields of `NativeCarryRepresentationCore`. -/
theorem minimalNativeCarryRepresentation : NativeCarryRepresentationCore := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact canonicalBR2CarryAmplitudeRatio_pow_sq_eq_carryMass
  · exact carryWeightedVerticalTfvd_identity
  · exact nativeLogGenerator_isSelfAdjoint
  · exact nativeLogGenerator_basisVector_log
  · intro camera cutoff hcamera s hs
    exact completedNativeCharacteristic_eq_factor_mul_nativeScalar hcamera hs

/-! ## Immediate representation and downstream corollaries -/

/-- The familiar four-channel formula is the energy polarization of exact
TFVD reconstruction at the positional carry ratio.  It is not an additional
field of the minimal core. -/
theorem nativeCarryRepresentationCore_reconstruct_apply
    (hcore : NativeCarryRepresentationCore)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (x : CarryVerticalL2) :
    carryVerticalL2WeightedGreen q
          (carryWeightedVerticalCenteredBracket q x) +
        carryWeightedVerticalReturn q hqpos.le hq1
          (carryWeightedVerticalTrace q x) = x := by
  have h := congrArg
    (fun T : CarryVerticalL2 →L[ℂ] CarryVerticalL2 => T x)
    (hcore.tfvdReconstruction q hqpos hq1)
  simpa using h

/-- The familiar four-channel formula is the inner-product polarization of
`nativeCarryRepresentationCore_reconstruct_apply`; it is not an additional
field of the minimal core. -/
theorem nativeCarryRepresentationCore_fourChannel
    (hcore : NativeCarryRepresentationCore)
    {base : ℕ} (hbase : IsSupported base) (x y : CarryVerticalL2) :
    let q := canonicalBR2CarryAmplitudeRatio base
    let Gx := carryVerticalL2WeightedGreen q
      (carryWeightedVerticalCenteredBracket q x)
    let Gy := carryVerticalL2WeightedGreen q
      (carryWeightedVerticalCenteredBracket q y)
    let Rx := carryWeightedVerticalReturn q
      (canonicalBR2CarryAmplitudeRatio_pos hbase).le
      (canonicalBR2CarryAmplitudeRatio_lt_one hbase)
      (carryWeightedVerticalTrace q x)
    let Ry := carryWeightedVerticalReturn q
      (canonicalBR2CarryAmplitudeRatio_pos hbase).le
      (canonicalBR2CarryAmplitudeRatio_lt_one hbase)
      (carryWeightedVerticalTrace q y)
    inner ℂ x y =
      inner ℂ Gx Gy + inner ℂ Gx Ry + inner ℂ Rx Gy + inner ℂ Rx Ry := by
  dsimp only
  have hx : carryVerticalL2WeightedGreen (canonicalBR2CarryAmplitudeRatio base)
        (carryWeightedVerticalCenteredBracket (canonicalBR2CarryAmplitudeRatio base) x) +
      carryWeightedVerticalReturn (canonicalBR2CarryAmplitudeRatio base)
        (canonicalBR2CarryAmplitudeRatio_pos hbase).le
        (canonicalBR2CarryAmplitudeRatio_lt_one hbase)
        (carryWeightedVerticalTrace (canonicalBR2CarryAmplitudeRatio base) x) = x :=
    nativeCarryRepresentationCore_reconstruct_apply hcore _
      (canonicalBR2CarryAmplitudeRatio_pos hbase)
      (canonicalBR2CarryAmplitudeRatio_lt_one hbase) x
  have hy : carryVerticalL2WeightedGreen (canonicalBR2CarryAmplitudeRatio base)
        (carryWeightedVerticalCenteredBracket (canonicalBR2CarryAmplitudeRatio base) y) +
      carryWeightedVerticalReturn (canonicalBR2CarryAmplitudeRatio base)
        (canonicalBR2CarryAmplitudeRatio_pos hbase).le
        (canonicalBR2CarryAmplitudeRatio_lt_one hbase)
        (carryWeightedVerticalTrace (canonicalBR2CarryAmplitudeRatio base) y) = y :=
    nativeCarryRepresentationCore_reconstruct_apply hcore _
      (canonicalBR2CarryAmplitudeRatio_pos hbase)
      (canonicalBR2CarryAmplitudeRatio_lt_one hbase) y
  calc
    inner ℂ x y = inner ℂ _ _ := congrArg₂ (inner ℂ) hx.symm hy.symm
    _ = _ := by
      simp only [inner_add_left, inner_add_right]
      ring

/-- The moment/Jacobi/finite-height presentation is downstream.  It is exact
once the already-existing Stieltjes positivity certificate is supplied; that
certificate is deliberately not asserted by `NativeCarryRepresentationCore`.
-/
theorem nativeCarryRepresentation_camera_to_finiteHeight
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff N : ℕ)
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :
    normalizedCompletedNativeCameraCharacteristic camera cutoff =
        (fun time : ℝ ↦ completedNativeOperatorCharacteristic (time : ℂ)) ∧
      completedNativeCameraLogDerivativeMoment camera cutoff =
        canonicalCompletedNativeLogDerivativeMoment ∧
      (∃ hgram :
          (hankelGram (completedNativeCameraLogDerivativeMoment camera cutoff) N).PosDef,
        canonicalFiniteJacobiSection
            (completedNativeCameraLogDerivativeMoment camera cutoff) N hgram =
          canonicalCompletedNativeStieltjesFiniteJacobiTower hpos N) ∧
      (nativeGeometryFiniteHeightOperator hpos N).IsSymm :=
  nativeGeometry_to_finiteHeight_chain hcamera cutoff N hpos

/-- Public Genuine-zero confinement remains a separate, single-gate frontier.
The core is an unconditional geometric representation theorem, but it does
not assert the scalar Green/Wronskian identity required by this implication.
-/
theorem nativeCarryRepresentation_minimalPublicSeam_to_confinement
    (hseam : MinimalPublicC3ConfinementSeam) :
    NativeCarryC3Crosswalk.FinalGenuineZeroConfinement :=
  finalGenuineZeroConfinement_of_minimalPublicC3Seam hseam

end

end CarrySelfAdjointOperator
