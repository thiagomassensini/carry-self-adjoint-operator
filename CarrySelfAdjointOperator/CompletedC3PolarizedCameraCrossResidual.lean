import CarrySelfAdjointOperator.CompletedC3EnrichedSymplecticNoLeakBridge
import NativeCarrySpectralWeyl.Camera.DerivativeTail
import NativeCarrySpectralWeyl.Camera.QuantitativeTail

/-!
# Polarized finite-camera cross residual

The finite camera cross identity is retained first as a value channel and a
log-jet channel.  Polarization and the height rotation are applied only after
those two channels have been formed.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Boundary
open Filter

noncomputable section

/-- Left value trace in the finite cross-factor identity. -/
def finiteCameraCrossLeftValue
    (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  factor 3 s * finiteBracketCharacteristic camera cutoff s

/-- Right value trace in the finite cross-factor identity. -/
def finiteCameraCrossRightValue
    (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  factor camera s * finiteBracketCharacteristic 3 cutoff s

/-- Finite cross-factor value residual between camera `camera` and the
canonical camera `3`. -/
def finiteCameraCrossValueResidual
    (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  finiteCameraCrossLeftValue camera cutoff s -
    finiteCameraCrossRightValue camera cutoff s

/-- Left log-jet trace, before height rotation. -/
def finiteCameraCrossLeftLogJet
    (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  -deriv (finiteCameraCrossLeftValue camera cutoff) s

/-- Right log-jet trace, before height rotation. -/
def finiteCameraCrossRightLogJet
    (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  -deriv (finiteCameraCrossRightValue camera cutoff) s

/-- The log-jet channel associated with the finite camera cross residual.
The minus sign is retained before any height-coordinate rotation. -/
def finiteCameraCrossLogJetResidual
    (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  -deriv (finiteCameraCrossValueResidual camera cutoff) s

/-- Infinite cross-factor residual. -/
def cameraCrossValueResidual (camera : ℕ) (s : ℂ) : ℂ :=
  factor 3 s * bracketCharacteristic camera s -
    factor camera s * bracketCharacteristic 3 s

/-- Infinite log-jet cross residual, still before height rotation. -/
def cameraCrossLogJetResidual (camera : ℕ) (s : ℂ) : ℂ :=
  -deriv (cameraCrossValueResidual camera) s

/-- Left value trace in the infinite cross-factor identity. -/
def cameraCrossLeftValue (camera : ℕ) (s : ℂ) : ℂ :=
  factor 3 s * bracketCharacteristic camera s

/-- Right value trace in the infinite cross-factor identity. -/
def cameraCrossRightValue (camera : ℕ) (s : ℂ) : ℂ :=
  factor camera s * bracketCharacteristic 3 s

/-- Left infinite log-jet trace. -/
def cameraCrossLeftLogJet (camera : ℕ) (s : ℂ) : ℂ :=
  -deriv (cameraCrossLeftValue camera) s

/-- Right infinite log-jet trace. -/
def cameraCrossRightLogJet (camera : ℕ) (s : ℂ) : ℂ :=
  -deriv (cameraCrossRightValue camera) s

/-! ## Exact completed camera traces -/

/-- Left value trace after adjoining the exact whole-center tail at the same
cutoff as the finite camera head. -/
def completedCameraCrossLeftValue
    (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  factor 3 s * completedNativeCharacteristic camera cutoff s

/-- Right value trace after adjoining the exact C3 whole-center tail. -/
def completedCameraCrossRightValue
    (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  factor camera s * completedNativeCharacteristic 3 cutoff s

/-- Completed left log-jet, retained before the height rotation. -/
def completedCameraCrossLeftLogJet
    (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  -deriv (completedCameraCrossLeftValue camera cutoff) s

/-- Completed right log-jet, retained before the height rotation. -/
def completedCameraCrossRightLogJet
    (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  -deriv (completedCameraCrossRightValue camera cutoff) s

/-- Camera-weighted value projection of the tail-completed enriched C3 TFVD
carrier. -/
def canonicalCompletedC3CameraWeightedTfvdValueTrace
    (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  factor camera s *
    canonicalCompletedC3FiniteEnrichedTfvdValueTailReadout cutoff s

/-- Log-jet of the same camera-weighted completed TFVD value projection. -/
def canonicalCompletedC3CameraWeightedTfvdLogJetTrace
    (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  -deriv (canonicalCompletedC3CameraWeightedTfvdValueTrace camera cutoff) s

/-- Polarized residual of the finite cross identity.  Each side is polarized
before subtraction. -/
def finitePolarizedCameraCrossResidual
    (camera cutoff : ℕ) (z w : ℂ) : ℂ :=
  mixedScalarBoundaryWedge
      (finiteCameraCrossLeftValue camera cutoff z)
      (finiteCameraCrossLeftLogJet camera cutoff z)
      (finiteCameraCrossLeftValue camera cutoff w)
      (finiteCameraCrossLeftLogJet camera cutoff w) -
    mixedScalarBoundaryWedge
      (finiteCameraCrossRightValue camera cutoff z)
      (finiteCameraCrossRightLogJet camera cutoff z)
      (finiteCameraCrossRightValue camera cutoff w)
      (finiteCameraCrossRightLogJet camera cutoff w)

/-- Height-coordinate polarization.  The log-jet channels remain separate
until both receive the final multiplication by `i`. -/
def finiteHeightPolarizedCameraCrossResidual
    (camera cutoff : ℕ) (z w : ℂ) : ℂ :=
  mixedScalarBoundaryWedge
      (finiteCameraCrossLeftValue camera cutoff z)
      (Complex.I * finiteCameraCrossLeftLogJet camera cutoff z)
      (finiteCameraCrossLeftValue camera cutoff w)
      (Complex.I * finiteCameraCrossLeftLogJet camera cutoff w) -
    mixedScalarBoundaryWedge
      (finiteCameraCrossRightValue camera cutoff z)
      (Complex.I * finiteCameraCrossRightLogJet camera cutoff z)
      (finiteCameraCrossRightValue camera cutoff w)
      (Complex.I * finiteCameraCrossRightLogJet camera cutoff w)

/-- Infinite polarized cross residual. -/
def polarizedCameraCrossResidual (camera : ℕ) (z w : ℂ) : ℂ :=
  mixedScalarBoundaryWedge
      (cameraCrossLeftValue camera z)
      (cameraCrossLeftLogJet camera z)
      (cameraCrossLeftValue camera w)
      (cameraCrossLeftLogJet camera w) -
    mixedScalarBoundaryWedge
      (cameraCrossRightValue camera z)
      (cameraCrossRightLogJet camera z)
      (cameraCrossRightValue camera w)
      (cameraCrossRightLogJet camera w)

/-- Infinite polarized cross residual after the final height rotation. -/
def heightPolarizedCameraCrossResidual
    (camera : ℕ) (z w : ℂ) : ℂ :=
  mixedScalarBoundaryWedge
      (cameraCrossLeftValue camera z)
      (Complex.I * cameraCrossLeftLogJet camera z)
      (cameraCrossLeftValue camera w)
      (Complex.I * cameraCrossLeftLogJet camera w) -
    mixedScalarBoundaryWedge
      (cameraCrossRightValue camera z)
      (Complex.I * cameraCrossRightLogJet camera z)
      (cameraCrossRightValue camera w)
      (Complex.I * cameraCrossRightLogJet camera w)

/-- Height-coordinate specialization used by the completed C3 ledger. -/
def canonicalC3FiniteHeightPolarizedCameraCrossResidual
    (camera cutoff : ℕ) (z w : ℂ) : ℂ :=
  finiteHeightPolarizedCameraCrossResidual camera cutoff
    (operatorHeightParameter z) (operatorHeightParameter w)

/-! ## Uncollapsed vector carriers -/

/-- Four-channel carrier of the polarized camera-cross expansion.  The two
positive and two negative bilinear contributions remain independent until
the final scalar readout. -/
abbrev PolarizedCameraCrossResidualChannelHilbert :=
  WithLp 2 (ℂ × WithLp 2 (ℂ × WithLp 2 (ℂ × ℂ)))

/-- Four boundary traces retained before polarization: value and log-jet at
`z`, followed by value and log-jet at `w`. -/
abbrev CameraCrossTraceHilbert :=
  WithLp 2 (ℂ × WithLp 2 (ℂ × WithLp 2 (ℂ × ℂ)))

/-- Left completed four-trace state. -/
def completedCameraCrossLeftTraceState
    (camera cutoff : ℕ) (z w : ℂ) : CameraCrossTraceHilbert :=
  WithLp.toLp 2
    (completedCameraCrossLeftValue camera cutoff z,
      WithLp.toLp 2
        (completedCameraCrossLeftLogJet camera cutoff z,
          WithLp.toLp 2
            (completedCameraCrossLeftValue camera cutoff w,
              completedCameraCrossLeftLogJet camera cutoff w)))

/-- Right completed four-trace state. -/
def completedCameraCrossRightTraceState
    (camera cutoff : ℕ) (z w : ℂ) : CameraCrossTraceHilbert :=
  WithLp.toLp 2
    (completedCameraCrossRightValue camera cutoff z,
      WithLp.toLp 2
        (completedCameraCrossRightLogJet camera cutoff z,
          WithLp.toLp 2
            (completedCameraCrossRightValue camera cutoff w,
              completedCameraCrossRightLogJet camera cutoff w)))

/-- The same four traces read through the tail-completed enriched C3 TFVD
carrier and weighted for camera `camera`. -/
def canonicalCompletedC3CameraWeightedTfvdTraceState
    (camera cutoff : ℕ) (z w : ℂ) : CameraCrossTraceHilbert :=
  WithLp.toLp 2
    (canonicalCompletedC3CameraWeightedTfvdValueTrace camera cutoff z,
      WithLp.toLp 2
        (canonicalCompletedC3CameraWeightedTfvdLogJetTrace camera cutoff z,
          WithLp.toLp 2
            (canonicalCompletedC3CameraWeightedTfvdValueTrace
                camera cutoff w,
              canonicalCompletedC3CameraWeightedTfvdLogJetTrace
                camera cutoff w)))

/-- Universal four-channel polarization of two complete boundary trace
quadruples.  Companions are supplied after any coordinate rotation. -/
def polarizedCrossResidualChannelState
    (leftValueZ leftCompanionZ leftValueW leftCompanionW : ℂ)
    (rightValueZ rightCompanionZ rightValueW rightCompanionW : ℂ) :
    PolarizedCameraCrossResidualChannelHilbert :=
  WithLp.toLp 2
    ((leftCompanionZ - rightCompanionZ) *
        (starRingEnd ℂ) leftValueW,
      WithLp.toLp 2
        (rightCompanionZ *
            (starRingEnd ℂ) (leftValueW - rightValueW),
          WithLp.toLp 2
            (-((leftValueZ - rightValueZ) *
                (starRingEnd ℂ) leftCompanionW),
              -(rightValueZ *
                (starRingEnd ℂ)
                (leftCompanionW - rightCompanionW)))))

/-- Completed four-channel residual formed only after all four traces have
been retained separately and the log-jet coordinates have been rotated. -/
def completedHeightPolarizedCameraCrossResidualChannelState
    (camera cutoff : ℕ) (z w : ℂ) :
    PolarizedCameraCrossResidualChannelHilbert :=
  polarizedCrossResidualChannelState
    (completedCameraCrossLeftValue camera cutoff z)
    (Complex.I * completedCameraCrossLeftLogJet camera cutoff z)
    (completedCameraCrossLeftValue camera cutoff w)
    (Complex.I * completedCameraCrossLeftLogJet camera cutoff w)
    (completedCameraCrossRightValue camera cutoff z)
    (Complex.I * completedCameraCrossRightLogJet camera cutoff z)
    (completedCameraCrossRightValue camera cutoff w)
    (Complex.I * completedCameraCrossRightLogJet camera cutoff w)

/-- Four-channel difference of two complete Green boundary polarizations in
one Hilbert carrier. -/
def greenFormPolarizedCrossResidualChannelState
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (leftDirect leftReflected rightDirect rightReflected : H × H) :
    PolarizedCameraCrossResidualChannelHilbert :=
  WithLp.toLp 2
    (inner ℂ leftDirect.2 (leftReflected.1 - rightReflected.1),
      WithLp.toLp 2
        (inner ℂ (leftDirect.2 - rightDirect.2) rightReflected.1,
          WithLp.toLp 2
            (-inner ℂ leftDirect.1 (leftReflected.2 - rightReflected.2),
              -inner ℂ (leftDirect.1 - rightDirect.1) rightReflected.2)))

/-- Common Hilbert carrier containing both a scalar TFVD trace and the
finite C3 Green boundary space without identifying either one by division. -/
abbrev CanonicalC3FiniteMixedHeightPolarizedCommonHilbert (M : ℕ) :=
  WithLp 2 (ℂ × FiniteC3GreenBoundarySpace (3 * M))

/-- Isometric coordinate injection of a scalar trace into the common
carrier. -/
def canonicalC3FiniteMixedHeightScalarEmbedding
    (M : ℕ) (value : ℂ) :
    CanonicalC3FiniteMixedHeightPolarizedCommonHilbert M :=
  WithLp.toLp 2 (value, 0)

/-- Isometric coordinate injection of a finite Green leg into the common
carrier. -/
def canonicalC3FiniteMixedHeightGreenEmbedding
    {M : ℕ} (value : FiniteC3GreenBoundarySpace (3 * M)) :
    CanonicalC3FiniteMixedHeightPolarizedCommonHilbert M :=
  WithLp.toLp 2 (0, value)

/-- Scalar boundary pair embedded into the common carrier. -/
def canonicalC3FiniteMixedHeightScalarBoundaryPair
    (M : ℕ) (companion value : ℂ) :
    CanonicalC3FiniteMixedHeightPolarizedCommonHilbert M ×
      CanonicalC3FiniteMixedHeightPolarizedCommonHilbert M :=
  (canonicalC3FiniteMixedHeightScalarEmbedding M companion,
    canonicalC3FiniteMixedHeightScalarEmbedding M value)

/-- Finite Green boundary pair embedded into the common carrier. -/
def canonicalC3FiniteMixedHeightGreenBoundaryPair
    {M : ℕ} (pair : FiniteC3GreenPortCarrier (3 * M)) :
    CanonicalC3FiniteMixedHeightPolarizedCommonHilbert M ×
      CanonicalC3FiniteMixedHeightPolarizedCommonHilbert M :=
  (canonicalC3FiniteMixedHeightGreenEmbedding pair.1,
    canonicalC3FiniteMixedHeightGreenEmbedding pair.2)

/-- First contribution: the `z` log-jet residual against the left value at
`w`. -/
def finiteHeightPolarizedCameraCrossZLogResidualChannel
    (camera cutoff : ℕ) (z w : ℂ) : ℂ :=
  (Complex.I * finiteCameraCrossLogJetResidual camera cutoff z) *
    (starRingEnd ℂ) (finiteCameraCrossLeftValue camera cutoff w)

/-- Second contribution: the retained right log-jet at `z` against the `w`
value residual. -/
def finiteHeightPolarizedCameraCrossWValueResidualChannel
    (camera cutoff : ℕ) (z w : ℂ) : ℂ :=
  (Complex.I * finiteCameraCrossRightLogJet camera cutoff z) *
    (starRingEnd ℂ) (finiteCameraCrossValueResidual camera cutoff w)

/-- Third, signed contribution: the `z` value residual against the retained
left log-jet at `w`. -/
def finiteHeightPolarizedCameraCrossZValueResidualChannel
    (camera cutoff : ℕ) (z w : ℂ) : ℂ :=
  -(finiteCameraCrossValueResidual camera cutoff z *
    (starRingEnd ℂ)
      (Complex.I * finiteCameraCrossLeftLogJet camera cutoff w))

/-- Fourth, signed contribution: the retained right value at `z` against the
`w` log-jet residual. -/
def finiteHeightPolarizedCameraCrossWLogResidualChannel
    (camera cutoff : ℕ) (z w : ℂ) : ℂ :=
  -(finiteCameraCrossRightValue camera cutoff z *
    (starRingEnd ℂ)
      (Complex.I * finiteCameraCrossLogJetResidual camera cutoff w))

/-- Honest four-channel state of the height-polarized camera cross residual. -/
def finiteHeightPolarizedCameraCrossResidualChannelState
    (camera cutoff : ℕ) (z w : ℂ) :
    PolarizedCameraCrossResidualChannelHilbert :=
  WithLp.toLp 2
    (finiteHeightPolarizedCameraCrossZLogResidualChannel
        camera cutoff z w,
      WithLp.toLp 2
        (finiteHeightPolarizedCameraCrossWValueResidualChannel
            camera cutoff z w,
          WithLp.toLp 2
            (finiteHeightPolarizedCameraCrossZValueResidualChannel
                camera cutoff z w,
              finiteHeightPolarizedCameraCrossWLogResidualChannel
                camera cutoff z w)))

/-- Scalar synthesis of the four camera-cross channels. -/
def polarizedCameraCrossResidualChannelScalarReadout
    (state : PolarizedCameraCrossResidualChannelHilbert) : ℂ :=
  state.fst + state.snd.fst + state.snd.snd.fst + state.snd.snd.snd

/-- Local-minus-Green layer of the canonical C3 finite polarized ledger. -/
def canonicalC3FiniteMixedHeightLocalGreenResidualChannel
    (M : ℕ) (z w : ℂ) : ℂ :=
  CanonicalC3AllCutoffMixedSourceHilbert.greenProvenanceReadout
    M w (reflectedParameter z)
      (canonicalC3AllCutoffMixedSourcePrefixState M z w)

/-- Global synthesized four-leg polarization minus the sum of complete local
polarizations. -/
def canonicalC3FiniteMixedHeightGlobalLocalResidualChannel
    (M : ℕ) (z w : ℂ) : ℂ :=
  let state := canonicalC3AllCutoffMixedSourcePrefixState M z w
  let legs := state.mixedLegs M
  sameSEdgeBoundaryWedge
      (∑ i, legs.left i) (∑ i, legs.right i)
      (∑ i, legs.jetLeft i) (∑ i, legs.jetRight i) -
    ∑ i, sameSEdgeBoundaryWedge
      (legs.left i) (legs.right i) (legs.jetLeft i) (legs.jetRight i)

/-- Complete head polarization minus the global synthesized four-leg
polarization.  Value and height-rotated log-jet channels remain separate in
both terms. -/
def canonicalC3FiniteMixedHeightHeadGlobalResidualChannel
    (M : ℕ) (z w : ℂ) : ℂ :=
  let state := canonicalC3AllCutoffMixedSourcePrefixState M z w
  let legs := state.mixedLegs M
  mixedScalarBoundaryWedge
      (CanonicalC3AllCutoffMixedSourceHilbert.valueHeadReadout M state.zSource)
      (Complex.I *
        CanonicalC3AllCutoffMixedSourceHilbert.logJetHeadReadout M state.zSource)
      (CanonicalC3AllCutoffMixedSourceHilbert.valueHeadReadout M state.wSource)
      (Complex.I *
        CanonicalC3AllCutoffMixedSourceHilbert.logJetHeadReadout M state.wSource) -
    sameSEdgeBoundaryWedge
      (∑ i, legs.left i) (∑ i, legs.right i)
      (∑ i, legs.jetLeft i) (∑ i, legs.jetRight i)

/-- Three-layer polarized residual state before scalar telescoping. -/
def canonicalC3FiniteMixedHeightPolarizedLayerResidualState
    (M : ℕ) (z w : ℂ) : CanonicalC3MixedStructuralChannelHilbert :=
  WithLp.toLp 2
    (canonicalC3FiniteMixedHeightLocalGreenResidualChannel M z w,
      WithLp.toLp 2
        (canonicalC3FiniteMixedHeightGlobalLocalResidualChannel M z w,
          canonicalC3FiniteMixedHeightHeadGlobalResidualChannel M z w))

/-! ## Four-defect opening of the structural residual -/

/-- Synthesized right-side companion at `z`, before comparison with the
complete height companion. -/
def canonicalC3FiniteMixedHeightSynthesizedCompanionZ
    (M : ℕ) (z w : ℂ) : ℂ :=
  let legs := canonicalMixedBoundaryResidualLegs
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) z w
  ∑ i, legs.jetLeft i

/-- Synthesized right-side value at `z`. -/
def canonicalC3FiniteMixedHeightSynthesizedValueZ
    (M : ℕ) (z w : ℂ) : ℂ :=
  let legs := canonicalMixedBoundaryResidualLegs
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) z w
  ∑ i, legs.jetRight i

/-- Synthesized right-side value at `w`; the local right leg stores its
conjugate. -/
def canonicalC3FiniteMixedHeightSynthesizedValueW
    (M : ℕ) (z w : ℂ) : ℂ :=
  let legs := canonicalMixedBoundaryResidualLegs
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) z w
  (starRingEnd ℂ) (∑ i, legs.right i)

/-- Synthesized right-side companion at `w`; the local left leg stores its
conjugate. -/
def canonicalC3FiniteMixedHeightSynthesizedCompanionW
    (M : ℕ) (z w : ℂ) : ℂ :=
  let legs := canonicalMixedBoundaryResidualLegs
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) z w
  (starRingEnd ℂ) (∑ i, legs.left i)

/-- First structural polarized defect: the `z` companion synthesis residual
against the complete value readout at `w`. -/
def canonicalC3FiniteMixedHeightZLogResidualChannel
    (M : ℕ) (z w : ℂ) : ℂ :=
  let dataZ := canonicalBoundaryResidualData
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) z
  let dataW := canonicalBoundaryResidualData
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) w
  let legs := canonicalMixedBoundaryResidualLegs
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) z w
  mixedBoundaryJetLeftResidual (Complex.I * dataZ.logJetReadout) legs *
    (starRingEnd ℂ) dataW.valueReadout

/-- Second structural polarized defect: the retained synthesized `z`
companion against the `w` value synthesis residual. -/
def canonicalC3FiniteMixedHeightWValueResidualChannel
    (M : ℕ) (z w : ℂ) : ℂ :=
  let dataW := canonicalBoundaryResidualData
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) w
  let legs := canonicalMixedBoundaryResidualLegs
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) z w
  (∑ i, legs.jetLeft i) * mixedBoundaryRightResidual dataW.valueReadout legs

/-- Third, signed structural polarized defect: the `z` value synthesis
residual against the complete height companion at `w`. -/
def canonicalC3FiniteMixedHeightZValueResidualChannel
    (M : ℕ) (z w : ℂ) : ℂ :=
  let dataZ := canonicalBoundaryResidualData
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) z
  let dataW := canonicalBoundaryResidualData
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) w
  let legs := canonicalMixedBoundaryResidualLegs
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) z w
  (-(mixedBoundaryJetRightResidual dataZ.valueReadout legs *
    (starRingEnd ℂ) (Complex.I * dataW.logJetReadout)))

/-- Fourth, signed structural polarized defect: the retained synthesized `z`
value against the `w` companion synthesis residual. -/
def canonicalC3FiniteMixedHeightWLogResidualChannel
    (M : ℕ) (z w : ℂ) : ℂ :=
  let dataW := canonicalBoundaryResidualData
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) w
  let legs := canonicalMixedBoundaryResidualLegs
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) z w
  (-((∑ i, legs.jetRight i) *
    mixedBoundaryLeftResidual (Complex.I * dataW.logJetReadout) legs))

/-- The readout-residual coordinate `R` opened into the same four polarized
bilinear positions used by the finite camera cross residual. -/
def canonicalC3FiniteMixedHeightPolarizedReadoutResidualState
    (M : ℕ) (z w : ℂ) : PolarizedCameraCrossResidualChannelHilbert :=
  WithLp.toLp 2
    (canonicalC3FiniteMixedHeightZLogResidualChannel M z w,
      WithLp.toLp 2
        (canonicalC3FiniteMixedHeightWValueResidualChannel M z w,
          WithLp.toLp 2
            (canonicalC3FiniteMixedHeightZValueResidualChannel M z w,
              canonicalC3FiniteMixedHeightWLogResidualChannel M z w)))

/-- Expanded structural carrier retaining `P`, `O`, and all four polarized
components extracted from `R`. -/
abbrev CanonicalC3MixedExpandedStructuralChannelHilbert :=
  WithLp 2
    (ℂ × WithLp 2 (ℂ × PolarizedCameraCrossResidualChannelHilbert))

/-- Honest opening `P ⊕ O ⊕ D₁ ⊕ D₂ ⊕ D₃ ⊕ D₄`. -/
def canonicalC3FiniteMixedHeightExpandedStructuralState
    (M : ℕ) (z w : ℂ) :
    CanonicalC3MixedExpandedStructuralChannelHilbert :=
  WithLp.toLp 2
    (canonicalC3FiniteMixedHeightGreenProvenanceChannel M z w,
      WithLp.toLp 2
        (canonicalC3FiniteMixedHeightOffDiagonalChannel M z w,
          canonicalC3FiniteMixedHeightPolarizedReadoutResidualState M z w))

/-- Final scalar readout of the expanded six-channel structural carrier. -/
def canonicalC3MixedExpandedStructuralScalarReadout
    (state : CanonicalC3MixedExpandedStructuralChannelHilbert) : ℂ :=
  state.fst + state.snd.fst +
    polarizedCameraCrossResidualChannelScalarReadout state.snd.snd

/-- The complete structural defect `P+O+R` opened directly into four Green
polarization defects in the common scalar/finite-Green Hilbert carrier. -/
def canonicalC3FiniteMixedHeightFullPolarizedStructuralResidualState
    (M : ℕ) (z w : ℂ) : PolarizedCameraCrossResidualChannelHilbert :=
  let dataZ := canonicalBoundaryResidualData
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) z
  let dataW := canonicalBoundaryResidualData
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) w
  let headDirect := canonicalC3FiniteMixedHeightScalarBoundaryPair
    M (Complex.I * dataW.logJetReadout) dataW.valueReadout
  let headReflected := canonicalC3FiniteMixedHeightScalarBoundaryPair
    M (Complex.I * dataZ.logJetReadout) dataZ.valueReadout
  let greenDirect := canonicalC3FiniteMixedHeightGreenBoundaryPair
    (finiteC3GenuineBracketGreenBoundaryPair (3 * M) w)
  let greenReflected := canonicalC3FiniteMixedHeightGreenBoundaryPair
    (finiteC3GenuineBracketGreenBoundaryPair
      (3 * M) (reflectedParameter z))
  greenFormPolarizedCrossResidualChannelState
    headDirect headReflected greenDirect greenReflected

/-- Endpoint difference represented by the three polarized layers. -/
def canonicalC3FiniteMixedHeightTfvdGreenPolarizedResidual
    (M : ℕ) (z w : ℂ) : ℂ :=
  let dataZ := canonicalBoundaryResidualData
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) z
  let dataW := canonicalBoundaryResidualData
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) w
  mixedScalarBoundaryWedge
      dataZ.valueReadout (Complex.I * dataZ.logJetReadout)
      dataW.valueReadout (Complex.I * dataW.logJetReadout) -
    greenForm (𝕜 := ℂ)
      (finiteC3GenuineBracketGreenBoundaryPair (3 * M) w)
      (finiteC3GenuineBracketGreenBoundaryPair
        (3 * M) (reflectedParameter z))

/-! ## First control lemmas -/

/-- The existing finite-camera estimate is exactly the norm estimate for the
new value residual. -/
theorem finiteCameraCrossValueResidual_nativeLine_norm_le
    {camera cutoff : ℕ} (hcamera : 2 ≤ camera) (hcutoff : 1 ≤ cutoff)
    (t : ℝ) :
    ‖finiteCameraCrossValueResidual camera cutoff (nativeLine t)‖ ≤
      ((2 / 3 : ℝ) *
        (‖factor camera (nativeLine t)‖ * nativeTailConstant 3 t +
          ‖factor 3 (nativeLine t)‖ * nativeTailConstant camera t)) *
        (cutoff : ℝ) ^ (-(3 : ℝ) / 2) := by
  simpa only [finiteCameraCrossValueResidual, finiteCameraCrossLeftValue,
    finiteCameraCrossRightValue] using
    finiteBracketCharacteristic_cross_tail_le hcamera hcutoff t

/-- The value residual inherits the already formalized
`O(cutoff⁻³ᴟ²)` camera control. -/
theorem finiteCameraCrossValueResidual_nativeLine_isBigO
    {camera : ℕ} (hcamera : 2 ≤ camera) (t : ℝ) :
    (fun cutoff : ℕ =>
      finiteCameraCrossValueResidual camera cutoff (nativeLine t)) =O[atTop]
      (fun cutoff : ℕ => (cutoff : ℝ) ^ (-(3 : ℝ) / 2)) := by
  simpa only [finiteCameraCrossValueResidual, finiteCameraCrossLeftValue,
    finiteCameraCrossRightValue] using
    finiteBracketCharacteristic_cross_tail_isBigO hcamera t

/-- The value residual converges to zero on the full bracket domain.  This
uses the infinite cross-factor identity only after both finite camera limits
have been taken. -/
theorem finiteCameraCrossValueResidual_tendsto_zero
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    Tendsto (fun cutoff : ℕ =>
      finiteCameraCrossValueResidual camera cutoff s)
      atTop (nhds 0) := by
  have hcameraLimit := finiteBracketCharacteristic_tendsto hcamera hs
  have hthreeLimit := finiteBracketCharacteristic_tendsto
    (by omega : 2 ≤ 3) hs
  have hfactorThree : Tendsto (fun _ : ℕ => factor 3 s) atTop
      (nhds (factor 3 s)) := tendsto_const_nhds
  have hfactorCamera : Tendsto (fun _ : ℕ => factor camera s) atTop
      (nhds (factor camera s)) := tendsto_const_nhds
  have hlimit :=
    (hfactorThree.mul hcameraLimit).sub
      (hfactorCamera.mul hthreeLimit)
  have hcross := bracketCharacteristic_cross_eq hcamera hs
  simpa only [finiteCameraCrossValueResidual, finiteCameraCrossLeftValue,
    finiteCameraCrossRightValue, hcross, sub_self] using hlimit

/-- The infinite value residual is exactly zero throughout the bracket
domain. -/
theorem cameraCrossValueResidual_eq_zero
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    cameraCrossValueResidual camera s = 0 := by
  unfold cameraCrossValueResidual
  exact sub_eq_zero.mpr (bracketCharacteristic_cross_eq hcamera hs)

/-- The infinite log-jet residual is also zero.  The proof differentiates
the cross identity on a neighborhood rather than discarding factor
derivatives pointwise. -/
theorem cameraCrossLogJetResidual_eq_zero
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    cameraCrossLogJetResidual camera s = 0 := by
  have heq : cameraCrossValueResidual camera =ᶠ[nhds s]
      (fun _ : ℂ => 0) := by
    filter_upwards [isOpen_bracketDomain.mem_nhds hs] with u hu
    exact cameraCrossValueResidual_eq_zero hcamera hu
  unfold cameraCrossLogJetResidual
  rw [heq.deriv_eq]
  simp

/-- Pointwise convergence of the finite characteristic derivatives, obtained
from the existing locally uniform convergence theorem. -/
theorem deriv_finiteBracketCharacteristic_tendsto
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    Tendsto
      (fun cutoff : ℕ =>
        deriv (finiteBracketCharacteristic camera cutoff) s)
      atTop (nhds (deriv (bracketCharacteristic camera) s)) := by
  have hderivConvergence :=
    (finiteBracketCharacteristic_tendstoLocallyUniformlyOn hcamera).deriv
      (Filter.Eventually.of_forall fun cutoff =>
        (finiteBracketCharacteristic_differentiable hcamera cutoff).differentiableOn)
      isOpen_bracketDomain
  simpa only [Function.comp_apply] using hderivConvergence.tendsto_at hs

/-- Product-rule expansion of the cross residual before the minus derivative
is renamed as the log-jet channel. -/
theorem hasDerivAt_finiteCameraCrossValueResidual
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (s : ℂ) :
    HasDerivAt (finiteCameraCrossValueResidual camera cutoff)
      (deriv (factor 3) s * finiteBracketCharacteristic camera cutoff s +
          factor 3 s *
            finiteBracketCharacteristicExponentDeriv camera cutoff s -
        (deriv (factor camera) s * finiteBracketCharacteristic 3 cutoff s +
          factor camera s *
            finiteBracketCharacteristicExponentDeriv 3 cutoff s)) s := by
  unfold finiteCameraCrossValueResidual
  exact
    (((factor_differentiable (by omega : 2 ≤ 3)).differentiableAt.hasDerivAt.mul
        (finiteBracketCharacteristic_hasDerivAt hcamera cutoff s)).sub
      ((factor_differentiable hcamera).differentiableAt.hasDerivAt.mul
        (finiteBracketCharacteristic_hasDerivAt (by omega : 2 ≤ 3) cutoff s)))

/-- Explicit separated formula for the log-jet residual.  In particular the
derivatives of the camera factors are retained. -/
theorem finiteCameraCrossLogJetResidual_eq
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (s : ℂ) :
    finiteCameraCrossLogJetResidual camera cutoff s =
      -(deriv (factor 3) s * finiteBracketCharacteristic camera cutoff s +
          factor 3 s *
            finiteBracketCharacteristicExponentDeriv camera cutoff s -
        (deriv (factor camera) s * finiteBracketCharacteristic 3 cutoff s +
          factor camera s *
            finiteBracketCharacteristicExponentDeriv 3 cutoff s)) := by
  unfold finiteCameraCrossLogJetResidual
  rw [(hasDerivAt_finiteCameraCrossValueResidual hcamera cutoff s).deriv]

/-- The same finite log-jet expansion, stated using ordinary derivatives of
the two finite characteristics. -/
theorem finiteCameraCrossLogJetResidual_eq_deriv
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (s : ℂ) :
    finiteCameraCrossLogJetResidual camera cutoff s =
      -(deriv (factor 3) s * finiteBracketCharacteristic camera cutoff s +
          factor 3 s * deriv (finiteBracketCharacteristic camera cutoff) s -
        (deriv (factor camera) s * finiteBracketCharacteristic 3 cutoff s +
          factor camera s *
            deriv (finiteBracketCharacteristic 3 cutoff) s)) := by
  rw [finiteCameraCrossLogJetResidual_eq hcamera]
  rw [deriv_finiteBracketCharacteristic hcamera,
    deriv_finiteBracketCharacteristic (by omega : 2 ≤ 3)]

/-- Product-rule expansion of the infinite cross residual. -/
theorem hasDerivAt_cameraCrossValueResidual
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    HasDerivAt (cameraCrossValueResidual camera)
      (deriv (factor 3) s * bracketCharacteristic camera s +
          factor 3 s * deriv (bracketCharacteristic camera) s -
        (deriv (factor camera) s * bracketCharacteristic 3 s +
          factor camera s * deriv (bracketCharacteristic 3) s)) s := by
  have hcameraCharacteristic :
      DifferentiableAt ℂ (bracketCharacteristic camera) s :=
    (bracketCharacteristic_differentiableOn hcamera).differentiableAt
      (isOpen_bracketDomain.mem_nhds hs)
  have hthreeCharacteristic :
      DifferentiableAt ℂ (bracketCharacteristic 3) s :=
    (bracketCharacteristic_differentiableOn (by omega : 2 ≤ 3)).differentiableAt
      (isOpen_bracketDomain.mem_nhds hs)
  unfold cameraCrossValueResidual
  exact
    (((factor_differentiable (by omega : 2 ≤ 3)).differentiableAt.hasDerivAt.mul
        hcameraCharacteristic.hasDerivAt).sub
      ((factor_differentiable hcamera).differentiableAt.hasDerivAt.mul
        hthreeCharacteristic.hasDerivAt))

/-- Infinite log-jet expansion with all factor derivatives retained. -/
theorem cameraCrossLogJetResidual_eq_deriv
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    cameraCrossLogJetResidual camera s =
      -(deriv (factor 3) s * bracketCharacteristic camera s +
          factor 3 s * deriv (bracketCharacteristic camera) s -
        (deriv (factor camera) s * bracketCharacteristic 3 s +
          factor camera s * deriv (bracketCharacteristic 3) s)) := by
  unfold cameraCrossLogJetResidual
  rw [(hasDerivAt_cameraCrossValueResidual hcamera hs).deriv]

/-- The finite log-jet cross residual converges to zero on the bracket domain.
This is the derivative-level counterpart of the value-channel limit. -/
theorem finiteCameraCrossLogJetResidual_tendsto_zero
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    Tendsto (fun cutoff : ℕ =>
      finiteCameraCrossLogJetResidual camera cutoff s)
      atTop (nhds 0) := by
  have hcameraValue := finiteBracketCharacteristic_tendsto hcamera hs
  have hthreeValue := finiteBracketCharacteristic_tendsto
    (by omega : 2 ≤ 3) hs
  have hcameraDeriv :=
    deriv_finiteBracketCharacteristic_tendsto hcamera hs
  have hthreeDeriv :=
    deriv_finiteBracketCharacteristic_tendsto (by omega : 2 ≤ 3) hs
  have hfactorThree : Tendsto (fun _ : ℕ => factor 3 s) atTop
      (nhds (factor 3 s)) := tendsto_const_nhds
  have hfactorCamera : Tendsto (fun _ : ℕ => factor camera s) atTop
      (nhds (factor camera s)) := tendsto_const_nhds
  have hfactorThreeDeriv : Tendsto (fun _ : ℕ => deriv (factor 3) s) atTop
      (nhds (deriv (factor 3) s)) := tendsto_const_nhds
  have hfactorCameraDeriv :
      Tendsto (fun _ : ℕ => deriv (factor camera) s) atTop
        (nhds (deriv (factor camera) s)) := tendsto_const_nhds
  have hleft :=
    (hfactorThreeDeriv.mul hcameraValue).add
      (hfactorThree.mul hcameraDeriv)
  have hright :=
    (hfactorCameraDeriv.mul hthreeValue).add
      (hfactorCamera.mul hthreeDeriv)
  have hformula := (hleft.sub hright).neg
  have hlimit : Tendsto (fun cutoff : ℕ =>
      finiteCameraCrossLogJetResidual camera cutoff s)
      atTop (nhds (cameraCrossLogJetResidual camera s)) := by
    simpa only [finiteCameraCrossLogJetResidual_eq_deriv hcamera,
      cameraCrossLogJetResidual_eq_deriv hcamera hs] using hformula
  simpa only [cameraCrossLogJetResidual_eq_zero hcamera hs] using hlimit

/-! ## Convergence of the two polarized sides -/

theorem hasDerivAt_finiteCameraCrossLeftValue
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (s : ℂ) :
    HasDerivAt (finiteCameraCrossLeftValue camera cutoff)
      (deriv (factor 3) s * finiteBracketCharacteristic camera cutoff s +
        factor 3 s *
          deriv (finiteBracketCharacteristic camera cutoff) s) s := by
  unfold finiteCameraCrossLeftValue
  exact
    (factor_differentiable (by omega : 2 ≤ 3)).differentiableAt.hasDerivAt.mul
      (finiteBracketCharacteristic_differentiable hcamera cutoff).differentiableAt.hasDerivAt

theorem hasDerivAt_finiteCameraCrossRightValue
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (s : ℂ) :
    HasDerivAt (finiteCameraCrossRightValue camera cutoff)
      (deriv (factor camera) s * finiteBracketCharacteristic 3 cutoff s +
        factor camera s * deriv (finiteBracketCharacteristic 3 cutoff) s) s := by
  unfold finiteCameraCrossRightValue
  exact
    (factor_differentiable hcamera).differentiableAt.hasDerivAt.mul
      (finiteBracketCharacteristic_differentiable
        (by omega : 2 ≤ 3) cutoff).differentiableAt.hasDerivAt

theorem finiteCameraCrossLeftLogJet_eq
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (s : ℂ) :
    finiteCameraCrossLeftLogJet camera cutoff s =
      -(deriv (factor 3) s * finiteBracketCharacteristic camera cutoff s +
        factor 3 s * deriv (finiteBracketCharacteristic camera cutoff) s) := by
  unfold finiteCameraCrossLeftLogJet
  rw [(hasDerivAt_finiteCameraCrossLeftValue hcamera cutoff s).deriv]

theorem finiteCameraCrossRightLogJet_eq
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (s : ℂ) :
    finiteCameraCrossRightLogJet camera cutoff s =
      -(deriv (factor camera) s * finiteBracketCharacteristic 3 cutoff s +
        factor camera s * deriv (finiteBracketCharacteristic 3 cutoff) s) := by
  unfold finiteCameraCrossRightLogJet
  rw [(hasDerivAt_finiteCameraCrossRightValue hcamera cutoff s).deriv]

theorem hasDerivAt_cameraCrossLeftValue
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    HasDerivAt (cameraCrossLeftValue camera)
      (deriv (factor 3) s * bracketCharacteristic camera s +
        factor 3 s * deriv (bracketCharacteristic camera) s) s := by
  have hcharacteristic : DifferentiableAt ℂ (bracketCharacteristic camera) s :=
    (bracketCharacteristic_differentiableOn hcamera).differentiableAt
      (isOpen_bracketDomain.mem_nhds hs)
  unfold cameraCrossLeftValue
  exact
    (factor_differentiable (by omega : 2 ≤ 3)).differentiableAt.hasDerivAt.mul
      hcharacteristic.hasDerivAt

theorem hasDerivAt_cameraCrossRightValue
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    HasDerivAt (cameraCrossRightValue camera)
      (deriv (factor camera) s * bracketCharacteristic 3 s +
        factor camera s * deriv (bracketCharacteristic 3) s) s := by
  have hcharacteristic : DifferentiableAt ℂ (bracketCharacteristic 3) s :=
    (bracketCharacteristic_differentiableOn (by omega : 2 ≤ 3)).differentiableAt
      (isOpen_bracketDomain.mem_nhds hs)
  unfold cameraCrossRightValue
  exact
    (factor_differentiable hcamera).differentiableAt.hasDerivAt.mul
      hcharacteristic.hasDerivAt

theorem cameraCrossLeftLogJet_eq
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    cameraCrossLeftLogJet camera s =
      -(deriv (factor 3) s * bracketCharacteristic camera s +
        factor 3 s * deriv (bracketCharacteristic camera) s) := by
  unfold cameraCrossLeftLogJet
  rw [(hasDerivAt_cameraCrossLeftValue hcamera hs).deriv]

theorem cameraCrossRightLogJet_eq
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    cameraCrossRightLogJet camera s =
      -(deriv (factor camera) s * bracketCharacteristic 3 s +
        factor camera s * deriv (bracketCharacteristic 3) s) := by
  unfold cameraCrossRightLogJet
  rw [(hasDerivAt_cameraCrossRightValue hcamera hs).deriv]

theorem finiteCameraCrossLeftValue_tendsto
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    Tendsto (fun cutoff : ℕ => finiteCameraCrossLeftValue camera cutoff s)
      atTop (nhds (cameraCrossLeftValue camera s)) := by
  have hfactor : Tendsto (fun _ : ℕ => factor 3 s) atTop
      (nhds (factor 3 s)) := tendsto_const_nhds
  simpa only [finiteCameraCrossLeftValue, cameraCrossLeftValue] using
    hfactor.mul (finiteBracketCharacteristic_tendsto hcamera hs)

theorem finiteCameraCrossRightValue_tendsto
    {camera : ℕ} (_hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    Tendsto (fun cutoff : ℕ => finiteCameraCrossRightValue camera cutoff s)
      atTop (nhds (cameraCrossRightValue camera s)) := by
  have hfactor : Tendsto (fun _ : ℕ => factor camera s) atTop
      (nhds (factor camera s)) := tendsto_const_nhds
  simpa only [finiteCameraCrossRightValue, cameraCrossRightValue] using
    hfactor.mul (finiteBracketCharacteristic_tendsto
      (by omega : 2 ≤ 3) hs)

theorem finiteCameraCrossLeftLogJet_tendsto
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    Tendsto (fun cutoff : ℕ => finiteCameraCrossLeftLogJet camera cutoff s)
      atTop (nhds (cameraCrossLeftLogJet camera s)) := by
  have hvalue := finiteBracketCharacteristic_tendsto hcamera hs
  have hderiv := deriv_finiteBracketCharacteristic_tendsto hcamera hs
  have hfactor : Tendsto (fun _ : ℕ => factor 3 s) atTop
      (nhds (factor 3 s)) := tendsto_const_nhds
  have hfactorDeriv : Tendsto (fun _ : ℕ => deriv (factor 3) s) atTop
      (nhds (deriv (factor 3) s)) := tendsto_const_nhds
  have hformula := ((hfactorDeriv.mul hvalue).add (hfactor.mul hderiv)).neg
  simpa only [finiteCameraCrossLeftLogJet_eq hcamera,
    cameraCrossLeftLogJet_eq hcamera hs] using hformula

theorem finiteCameraCrossRightLogJet_tendsto
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    Tendsto (fun cutoff : ℕ => finiteCameraCrossRightLogJet camera cutoff s)
      atTop (nhds (cameraCrossRightLogJet camera s)) := by
  have hvalue := finiteBracketCharacteristic_tendsto
    (by omega : 2 ≤ 3) hs
  have hderiv := deriv_finiteBracketCharacteristic_tendsto
    (by omega : 2 ≤ 3) hs
  have hfactor : Tendsto (fun _ : ℕ => factor camera s) atTop
      (nhds (factor camera s)) := tendsto_const_nhds
  have hfactorDeriv :
      Tendsto (fun _ : ℕ => deriv (factor camera) s) atTop
        (nhds (deriv (factor camera) s)) := tendsto_const_nhds
  have hformula := ((hfactorDeriv.mul hvalue).add (hfactor.mul hderiv)).neg
  simpa only [finiteCameraCrossRightLogJet_eq hcamera,
    cameraCrossRightLogJet_eq hcamera hs] using hformula

theorem cameraCrossLeftValue_eq_rightValue
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    cameraCrossLeftValue camera s = cameraCrossRightValue camera s := by
  unfold cameraCrossLeftValue cameraCrossRightValue
  exact bracketCharacteristic_cross_eq hcamera hs

theorem cameraCrossLeftLogJet_eq_rightLogJet
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    cameraCrossLeftLogJet camera s = cameraCrossRightLogJet camera s := by
  have heq : cameraCrossLeftValue camera =ᶠ[nhds s]
      cameraCrossRightValue camera := by
    filter_upwards [isOpen_bracketDomain.mem_nhds hs] with u hu
    exact cameraCrossLeftValue_eq_rightValue hcamera hu
  unfold cameraCrossLeftLogJet cameraCrossRightLogJet
  rw [heq.deriv_eq]

/-! ## Exact equality of the four completed traces -/

/-- Completing the left finite head by its exact whole-center tail recovers
the left infinite trace at every cutoff. -/
theorem completedCameraCrossLeftValue_eq_cameraCrossLeftValue
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    completedCameraCrossLeftValue camera cutoff s =
      cameraCrossLeftValue camera s := by
  unfold completedCameraCrossLeftValue cameraCrossLeftValue
  rw [completedNativeCharacteristic_eq_bracketCharacteristic hcamera hs]

/-- Completing the right C3 head recovers the right infinite trace at every
cutoff. -/
theorem completedCameraCrossRightValue_eq_cameraCrossRightValue
    {camera : ℕ} (_hcamera : 2 ≤ camera) (cutoff : ℕ) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    completedCameraCrossRightValue camera cutoff s =
      cameraCrossRightValue camera s := by
  unfold completedCameraCrossRightValue cameraCrossRightValue
  rw [completedNativeCharacteristic_eq_bracketCharacteristic
    (by omega : 2 ≤ 3) hs]

/-- The completed C3 native head--tail trace and the completed enriched TFVD
value readout are the same finite-cutoff presentation of the C3 chart. -/
theorem canonicalCompletedC3FiniteEnrichedTfvdValueTailReadout_eq_completedNativeCharacteristic_three
    (cutoff : ℕ) {s : ℂ} (hs : s ∈ bracketDomain) :
    canonicalCompletedC3FiniteEnrichedTfvdValueTailReadout cutoff s =
      completedNativeCharacteristic 3 cutoff s := by
  have hsRe : -1 < s.re := by simpa [bracketDomain] using hs
  have hsHalf : s ∈ bracketHalfPlane := by
    simpa [bracketHalfPlane, bracketDomain] using hs
  calc
    canonicalCompletedC3FiniteEnrichedTfvdValueTailReadout cutoff s =
        bracketedDirichletChart 3 s := by
      exact
        NativeCarryC3Crosswalk.finiteC3CanonicalEnrichedTfvdPairTailReadout_eq_chart
          cutoff tfvdHaarScale_ne_zero (fun _ : ℕ => (1 : ℂ))
          (by intro m; norm_num) hsRe
    _ = bracketCharacteristic 3 s :=
      (bracketCharacteristic_three_eq_bracketedDirichletChart hsHalf).symm
    _ = completedNativeCharacteristic 3 cutoff s :=
      (completedNativeCharacteristic_eq_bracketCharacteristic
        (by omega : 2 ≤ 3) hs).symm

/-- The right camera trace is exactly the weighted value projection of the
completed enriched C3 TFVD carrier. -/
theorem completedCameraCrossRightValue_eq_weightedTfvdValueTrace
    (camera cutoff : ℕ) {s : ℂ} (hs : s ∈ bracketDomain) :
    completedCameraCrossRightValue camera cutoff s =
      canonicalCompletedC3CameraWeightedTfvdValueTrace camera cutoff s := by
  unfold completedCameraCrossRightValue
    canonicalCompletedC3CameraWeightedTfvdValueTrace
  rw [canonicalCompletedC3FiniteEnrichedTfvdValueTailReadout_eq_completedNativeCharacteristic_three
    cutoff hs]

/-- The right camera log-jet and the weighted completed TFVD log-jet are the
same derivative trace. -/
theorem completedCameraCrossRightLogJet_eq_weightedTfvdLogJetTrace
    (camera cutoff : ℕ) {s : ℂ} (hs : s ∈ bracketDomain) :
    completedCameraCrossRightLogJet camera cutoff s =
      canonicalCompletedC3CameraWeightedTfvdLogJetTrace camera cutoff s := by
  have heq : completedCameraCrossRightValue camera cutoff =ᶠ[nhds s]
      canonicalCompletedC3CameraWeightedTfvdValueTrace camera cutoff := by
    filter_upwards [isOpen_bracketDomain.mem_nhds hs] with u hu
    exact completedCameraCrossRightValue_eq_weightedTfvdValueTrace
      camera cutoff hu
  unfold completedCameraCrossRightLogJet
    canonicalCompletedC3CameraWeightedTfvdLogJetTrace
  rw [heq.deriv_eq]

/-- The two completed weighted value traces are exactly equal, independently
of the cutoff. -/
theorem completedCameraCrossLeftValue_eq_rightValue
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    completedCameraCrossLeftValue camera cutoff s =
      completedCameraCrossRightValue camera cutoff s := by
  calc
    completedCameraCrossLeftValue camera cutoff s =
        cameraCrossLeftValue camera s :=
      completedCameraCrossLeftValue_eq_cameraCrossLeftValue
        hcamera cutoff hs
    _ = cameraCrossRightValue camera s :=
      cameraCrossLeftValue_eq_rightValue hcamera hs
    _ = completedCameraCrossRightValue camera cutoff s :=
      (completedCameraCrossRightValue_eq_cameraCrossRightValue
        hcamera cutoff hs).symm

/-- The completed left log-jet is the log-jet of the same infinite weighted
camera trace.  The proof differentiates the head--tail identity on a
neighborhood. -/
theorem completedCameraCrossLeftLogJet_eq_cameraCrossLeftLogJet
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    completedCameraCrossLeftLogJet camera cutoff s =
      cameraCrossLeftLogJet camera s := by
  have heq : completedCameraCrossLeftValue camera cutoff =ᶠ[nhds s]
      cameraCrossLeftValue camera := by
    filter_upwards [isOpen_bracketDomain.mem_nhds hs] with u hu
    exact completedCameraCrossLeftValue_eq_cameraCrossLeftValue
      hcamera cutoff hu
  unfold completedCameraCrossLeftLogJet cameraCrossLeftLogJet
  rw [heq.deriv_eq]

/-- The completed right log-jet is the log-jet of the same infinite weighted
C3 trace. -/
theorem completedCameraCrossRightLogJet_eq_cameraCrossRightLogJet
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    completedCameraCrossRightLogJet camera cutoff s =
      cameraCrossRightLogJet camera s := by
  have heq : completedCameraCrossRightValue camera cutoff =ᶠ[nhds s]
      cameraCrossRightValue camera := by
    filter_upwards [isOpen_bracketDomain.mem_nhds hs] with u hu
    exact completedCameraCrossRightValue_eq_cameraCrossRightValue
      hcamera cutoff hu
  unfold completedCameraCrossRightLogJet cameraCrossRightLogJet
  rw [heq.deriv_eq]

/-- The two completed weighted log-jets are exactly equal.  No quotient or
zero-set specialization is used. -/
theorem completedCameraCrossLeftLogJet_eq_rightLogJet
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    completedCameraCrossLeftLogJet camera cutoff s =
      completedCameraCrossRightLogJet camera cutoff s := by
  calc
    completedCameraCrossLeftLogJet camera cutoff s =
        cameraCrossLeftLogJet camera s :=
      completedCameraCrossLeftLogJet_eq_cameraCrossLeftLogJet
        hcamera cutoff hs
    _ = cameraCrossRightLogJet camera s :=
      cameraCrossLeftLogJet_eq_rightLogJet hcamera hs
    _ = completedCameraCrossRightLogJet camera cutoff s :=
      (completedCameraCrossRightLogJet_eq_cameraCrossRightLogJet
        hcamera cutoff hs).symm

/-- Vector equality of all four completed traces: value and log-jet at `z`,
then value and log-jet at `w`.  The coordinates are identified before any
polarized scalar readout. -/
theorem completedCameraCrossLeftTraceState_eq_rightTraceState
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) {z w : ℂ}
    (hz : z ∈ bracketDomain) (hw : w ∈ bracketDomain) :
    completedCameraCrossLeftTraceState camera cutoff z w =
      completedCameraCrossRightTraceState camera cutoff z w := by
  unfold completedCameraCrossLeftTraceState
    completedCameraCrossRightTraceState
  rw [completedCameraCrossLeftValue_eq_rightValue hcamera cutoff hz,
    completedCameraCrossLeftLogJet_eq_rightLogJet hcamera cutoff hz,
    completedCameraCrossLeftValue_eq_rightValue hcamera cutoff hw,
    completedCameraCrossLeftLogJet_eq_rightLogJet hcamera cutoff hw]

/-- The four right-hand C3 traces are exactly the four projections of the
same completed enriched TFVD carrier. -/
theorem completedCameraCrossRightTraceState_eq_weightedTfvdTraceState
    (camera cutoff : ℕ) {z w : ℂ}
    (hz : z ∈ bracketDomain) (hw : w ∈ bracketDomain) :
    completedCameraCrossRightTraceState camera cutoff z w =
      canonicalCompletedC3CameraWeightedTfvdTraceState
        camera cutoff z w := by
  unfold completedCameraCrossRightTraceState
    canonicalCompletedC3CameraWeightedTfvdTraceState
  rw [completedCameraCrossRightValue_eq_weightedTfvdValueTrace
      camera cutoff hz,
    completedCameraCrossRightLogJet_eq_weightedTfvdLogJetTrace
      camera cutoff hz,
    completedCameraCrossRightValue_eq_weightedTfvdValueTrace
      camera cutoff hw,
    completedCameraCrossRightLogJet_eq_weightedTfvdLogJetTrace
      camera cutoff hw]

/-- Final four-trace identification: the global camera completion and the
weighted enriched TFVD/C3 readout are one vector, coordinate by coordinate. -/
theorem completedCameraCrossLeftTraceState_eq_weightedTfvdTraceState
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) {z w : ℂ}
    (hz : z ∈ bracketDomain) (hw : w ∈ bracketDomain) :
    completedCameraCrossLeftTraceState camera cutoff z w =
      canonicalCompletedC3CameraWeightedTfvdTraceState
        camera cutoff z w := by
  calc
    completedCameraCrossLeftTraceState camera cutoff z w =
        completedCameraCrossRightTraceState camera cutoff z w :=
      completedCameraCrossLeftTraceState_eq_rightTraceState
        hcamera cutoff hz hw
    _ = canonicalCompletedC3CameraWeightedTfvdTraceState
          camera cutoff z w :=
      completedCameraCrossRightTraceState_eq_weightedTfvdTraceState
        camera cutoff hz hw

/-- Because all four completed traces agree, every completed polarized defect
channel vanishes separately. -/
theorem completedHeightPolarizedCameraCrossResidualChannelState_eq_zero
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) {z w : ℂ}
    (hz : z ∈ bracketDomain) (hw : w ∈ bracketDomain) :
    completedHeightPolarizedCameraCrossResidualChannelState
        camera cutoff z w = 0 := by
  unfold completedHeightPolarizedCameraCrossResidualChannelState
  rw [completedCameraCrossLeftValue_eq_rightValue hcamera cutoff hz,
    completedCameraCrossLeftLogJet_eq_rightLogJet hcamera cutoff hz,
    completedCameraCrossLeftValue_eq_rightValue hcamera cutoff hw,
    completedCameraCrossLeftLogJet_eq_rightLogJet hcamera cutoff hw]
  simp [polarizedCrossResidualChannelState]

/-- The finite log-jet residual is exactly the difference of the two retained
log-jet sides. -/
theorem finiteCameraCrossLogJetResidual_eq_left_sub_right
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (s : ℂ) :
    finiteCameraCrossLogJetResidual camera cutoff s =
      finiteCameraCrossLeftLogJet camera cutoff s -
        finiteCameraCrossRightLogJet camera cutoff s := by
  unfold finiteCameraCrossLogJetResidual finiteCameraCrossValueResidual
    finiteCameraCrossLeftLogJet finiteCameraCrossRightLogJet
  have hleft := hasDerivAt_finiteCameraCrossLeftValue hcamera cutoff s
  have hright := hasDerivAt_finiteCameraCrossRightValue hcamera cutoff s
  have hsub := hleft.sub hright
  change -deriv
      (finiteCameraCrossLeftValue camera cutoff -
        finiteCameraCrossRightValue camera cutoff) s = _
  rw [hsub.deriv, hleft.deriv, hright.deriv]
  ring

/-- Four-term expansion of the polarized residual.  Every term contains an
explicit value or log-jet cross residual, so no cancellation is hidden inside
the final wedge subtraction. -/
theorem finitePolarizedCameraCrossResidual_eq_residualExpansion
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (z w : ℂ) :
    finitePolarizedCameraCrossResidual camera cutoff z w =
      finiteCameraCrossLogJetResidual camera cutoff z *
          (starRingEnd ℂ) (finiteCameraCrossLeftValue camera cutoff w) +
        finiteCameraCrossRightLogJet camera cutoff z *
          (starRingEnd ℂ) (finiteCameraCrossValueResidual camera cutoff w) -
        finiteCameraCrossValueResidual camera cutoff z *
          (starRingEnd ℂ) (finiteCameraCrossLeftLogJet camera cutoff w) -
        finiteCameraCrossRightValue camera cutoff z *
          (starRingEnd ℂ) (finiteCameraCrossLogJetResidual camera cutoff w) := by
  rw [finiteCameraCrossLogJetResidual_eq_left_sub_right hcamera cutoff z,
    finiteCameraCrossLogJetResidual_eq_left_sub_right hcamera cutoff w]
  unfold finitePolarizedCameraCrossResidual finiteCameraCrossValueResidual
    mixedScalarBoundaryWedge
  simp only [map_sub]
  ring

/-- Height-rotated version of the four-term residual expansion.  Rotation is
still applied only at this final polarized readout. -/
theorem finiteHeightPolarizedCameraCrossResidual_eq_residualExpansion
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (z w : ℂ) :
    finiteHeightPolarizedCameraCrossResidual camera cutoff z w =
      (Complex.I * finiteCameraCrossLogJetResidual camera cutoff z) *
          (starRingEnd ℂ) (finiteCameraCrossLeftValue camera cutoff w) +
        (Complex.I * finiteCameraCrossRightLogJet camera cutoff z) *
          (starRingEnd ℂ) (finiteCameraCrossValueResidual camera cutoff w) -
        finiteCameraCrossValueResidual camera cutoff z *
          (starRingEnd ℂ)
            (Complex.I * finiteCameraCrossLeftLogJet camera cutoff w) -
        finiteCameraCrossRightValue camera cutoff z *
          (starRingEnd ℂ)
            (Complex.I * finiteCameraCrossLogJetResidual camera cutoff w) := by
  rw [finiteCameraCrossLogJetResidual_eq_left_sub_right hcamera cutoff z,
    finiteCameraCrossLogJetResidual_eq_left_sub_right hcamera cutoff w]
  unfold finiteHeightPolarizedCameraCrossResidual
    finiteCameraCrossValueResidual mixedScalarBoundaryWedge
  simp only [mul_sub, map_sub]
  ring

/-! ## Vector identities before scalar synthesis -/

/-- Four Hilbert-space polarization channels recover the difference of the
two complete Green forms. -/
theorem polarizedCameraCrossResidualChannelScalarReadout_greenFormState
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (leftDirect leftReflected rightDirect rightReflected : H × H) :
    polarizedCameraCrossResidualChannelScalarReadout
        (greenFormPolarizedCrossResidualChannelState
          leftDirect leftReflected rightDirect rightReflected) =
      greenForm leftDirect leftReflected -
        greenForm rightDirect rightReflected := by
  unfold polarizedCameraCrossResidualChannelScalarReadout
    greenFormPolarizedCrossResidualChannelState greenForm
  change
    inner ℂ leftDirect.2 (leftReflected.1 - rightReflected.1) +
          inner ℂ (leftDirect.2 - rightDirect.2) rightReflected.1 +
        -inner ℂ leftDirect.1 (leftReflected.2 - rightReflected.2) +
      -inner ℂ (leftDirect.1 - rightDirect.1) rightReflected.2 = _
  simp only [inner_sub_left, inner_sub_right]
  ring

/-- The scalar four-defect constructor is literally the Hilbert Green-form
constructor specialized to `H = ℂ`. -/
theorem polarizedCrossResidualChannelState_eq_greenFormState_scalar
    (leftValueZ leftCompanionZ leftValueW leftCompanionW : ℂ)
    (rightValueZ rightCompanionZ rightValueW rightCompanionW : ℂ) :
    polarizedCrossResidualChannelState
        leftValueZ leftCompanionZ leftValueW leftCompanionW
        rightValueZ rightCompanionZ rightValueW rightCompanionW =
      greenFormPolarizedCrossResidualChannelState
        (leftCompanionW, leftValueW) (leftCompanionZ, leftValueZ)
        (rightCompanionW, rightValueW) (rightCompanionZ, rightValueZ) := by
  unfold polarizedCrossResidualChannelState
    greenFormPolarizedCrossResidualChannelState
  simp only [RCLike.inner_apply]

/-- The scalar embedding preserves the complete scalar boundary
polarization. -/
theorem greenForm_canonicalC3FiniteMixedHeightScalarBoundaryPair
    (M : ℕ) (companionW valueW companionZ valueZ : ℂ) :
    greenForm
        (canonicalC3FiniteMixedHeightScalarBoundaryPair
          M companionW valueW)
        (canonicalC3FiniteMixedHeightScalarBoundaryPair
          M companionZ valueZ) =
      mixedScalarBoundaryWedge valueZ companionZ valueW companionW := by
  simp [greenForm, mixedScalarBoundaryWedge,
    canonicalC3FiniteMixedHeightScalarBoundaryPair,
    canonicalC3FiniteMixedHeightScalarEmbedding,
    WithLp.prod_inner_apply, RCLike.inner_apply]

/-- The finite-Green embedding preserves the original vector Green form. -/
theorem greenForm_canonicalC3FiniteMixedHeightGreenBoundaryPair
    {M : ℕ} (direct reflected : FiniteC3GreenPortCarrier (3 * M)) :
    greenForm (𝕜 := ℂ)
        (canonicalC3FiniteMixedHeightGreenBoundaryPair direct)
        (canonicalC3FiniteMixedHeightGreenBoundaryPair reflected) =
      greenForm (𝕜 := ℂ) direct reflected := by
  simp [greenForm, canonicalC3FiniteMixedHeightGreenBoundaryPair,
    canonicalC3FiniteMixedHeightGreenEmbedding,
    WithLp.prod_inner_apply]

/-- Universal four-channel state reads as complete left polarization minus
complete right polarization. -/
theorem polarizedCameraCrossResidualChannelScalarReadout_genericState
    (leftValueZ leftCompanionZ leftValueW leftCompanionW : ℂ)
    (rightValueZ rightCompanionZ rightValueW rightCompanionW : ℂ) :
    polarizedCameraCrossResidualChannelScalarReadout
        (polarizedCrossResidualChannelState
          leftValueZ leftCompanionZ leftValueW leftCompanionW
          rightValueZ rightCompanionZ rightValueW rightCompanionW) =
      mixedScalarBoundaryWedge
          leftValueZ leftCompanionZ leftValueW leftCompanionW -
        mixedScalarBoundaryWedge
          rightValueZ rightCompanionZ rightValueW rightCompanionW := by
  unfold polarizedCameraCrossResidualChannelScalarReadout
    polarizedCrossResidualChannelState mixedScalarBoundaryWedge
  change
    (leftCompanionZ - rightCompanionZ) *
          (starRingEnd ℂ) leftValueW +
        rightCompanionZ *
          (starRingEnd ℂ) (leftValueW - rightValueW) +
      -((leftValueZ - rightValueZ) *
          (starRingEnd ℂ) leftCompanionW) +
    -(rightValueZ *
        (starRingEnd ℂ) (leftCompanionW - rightCompanionW)) = _
  simp only [map_sub]
  ring

/-- The finite camera state is an instance of the universal four-defect
polarization, with the height rotation applied before comparison. -/
theorem finiteHeightPolarizedCameraCrossResidualChannelState_eq_generic
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (z w : ℂ) :
    finiteHeightPolarizedCameraCrossResidualChannelState camera cutoff z w =
      polarizedCrossResidualChannelState
        (finiteCameraCrossLeftValue camera cutoff z)
        (Complex.I * finiteCameraCrossLeftLogJet camera cutoff z)
        (finiteCameraCrossLeftValue camera cutoff w)
        (Complex.I * finiteCameraCrossLeftLogJet camera cutoff w)
        (finiteCameraCrossRightValue camera cutoff z)
        (Complex.I * finiteCameraCrossRightLogJet camera cutoff z)
        (finiteCameraCrossRightValue camera cutoff w)
        (Complex.I * finiteCameraCrossRightLogJet camera cutoff w) := by
  unfold finiteHeightPolarizedCameraCrossResidualChannelState
    finiteHeightPolarizedCameraCrossZLogResidualChannel
    finiteHeightPolarizedCameraCrossWValueResidualChannel
    finiteHeightPolarizedCameraCrossZValueResidualChannel
    finiteHeightPolarizedCameraCrossWLogResidualChannel
    polarizedCrossResidualChannelState finiteCameraCrossValueResidual
  rw [finiteCameraCrossLogJetResidual_eq_left_sub_right hcamera cutoff z,
    finiteCameraCrossLogJetResidual_eq_left_sub_right hcamera cutoff w]
  congr 1
  ring_nf

/-- Camera realization stated in the same Hilbert Green-form constructor used
by the fully opened structural defect. -/
theorem finiteHeightPolarizedCameraCrossResidualChannelState_eq_greenFormState
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (z w : ℂ) :
    finiteHeightPolarizedCameraCrossResidualChannelState camera cutoff z w =
      greenFormPolarizedCrossResidualChannelState
        (Complex.I * finiteCameraCrossLeftLogJet camera cutoff w,
          finiteCameraCrossLeftValue camera cutoff w)
        (Complex.I * finiteCameraCrossLeftLogJet camera cutoff z,
          finiteCameraCrossLeftValue camera cutoff z)
        (Complex.I * finiteCameraCrossRightLogJet camera cutoff w,
          finiteCameraCrossRightValue camera cutoff w)
        (Complex.I * finiteCameraCrossRightLogJet camera cutoff z,
          finiteCameraCrossRightValue camera cutoff z) := by
  rw [finiteHeightPolarizedCameraCrossResidualChannelState_eq_generic
    hcamera cutoff z w]
  exact polarizedCrossResidualChannelState_eq_greenFormState_scalar
    (finiteCameraCrossLeftValue camera cutoff z)
    (Complex.I * finiteCameraCrossLeftLogJet camera cutoff z)
    (finiteCameraCrossLeftValue camera cutoff w)
    (Complex.I * finiteCameraCrossLeftLogJet camera cutoff w)
    (finiteCameraCrossRightValue camera cutoff z)
    (Complex.I * finiteCameraCrossRightLogJet camera cutoff z)
    (finiteCameraCrossRightValue camera cutoff w)
    (Complex.I * finiteCameraCrossRightLogJet camera cutoff w)

/-- The four-channel readout recovers the polarized camera cross residual.
This theorem is deliberately downstream of the vector state definition. -/
theorem polarizedCameraCrossResidualChannelScalarReadout_state
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (z w : ℂ) :
    polarizedCameraCrossResidualChannelScalarReadout
        (finiteHeightPolarizedCameraCrossResidualChannelState
          camera cutoff z w) =
      finiteHeightPolarizedCameraCrossResidual camera cutoff z w := by
  rw [finiteHeightPolarizedCameraCrossResidual_eq_residualExpansion
    hcamera cutoff z w]
  unfold polarizedCameraCrossResidualChannelScalarReadout
    finiteHeightPolarizedCameraCrossResidualChannelState
    finiteHeightPolarizedCameraCrossZLogResidualChannel
    finiteHeightPolarizedCameraCrossWValueResidualChannel
    finiteHeightPolarizedCameraCrossZValueResidualChannel
    finiteHeightPolarizedCameraCrossWLogResidualChannel
  change
    (Complex.I * finiteCameraCrossLogJetResidual camera cutoff z) *
          (starRingEnd ℂ) (finiteCameraCrossLeftValue camera cutoff w) +
        (Complex.I * finiteCameraCrossRightLogJet camera cutoff z) *
          (starRingEnd ℂ) (finiteCameraCrossValueResidual camera cutoff w) +
      -(finiteCameraCrossValueResidual camera cutoff z *
          (starRingEnd ℂ)
            (Complex.I * finiteCameraCrossLeftLogJet camera cutoff w)) +
    -(finiteCameraCrossRightValue camera cutoff z *
        (starRingEnd ℂ)
          (Complex.I * finiteCameraCrossLogJetResidual camera cutoff w)) = _
  ring

/-- The four structural polarized defects contract exactly to the existing
readout-residual coordinate `R`. -/
theorem canonicalC3MixedStructuralScalarReadout_polarizedResidualState
    (M : ℕ) (z w : ℂ) :
    polarizedCameraCrossResidualChannelScalarReadout
        (canonicalC3FiniteMixedHeightPolarizedReadoutResidualState M z w) =
      canonicalC3FiniteMixedHeightReadoutResidualChannel M z w := by
  change
    canonicalC3FiniteMixedHeightZLogResidualChannel M z w +
          canonicalC3FiniteMixedHeightWValueResidualChannel M z w +
        canonicalC3FiniteMixedHeightZValueResidualChannel M z w +
      canonicalC3FiniteMixedHeightWLogResidualChannel M z w = _
  unfold canonicalC3FiniteMixedHeightZLogResidualChannel
    canonicalC3FiniteMixedHeightWValueResidualChannel
    canonicalC3FiniteMixedHeightZValueResidualChannel
    canonicalC3FiniteMixedHeightWLogResidualChannel
    canonicalC3FiniteMixedHeightReadoutResidualChannel
    canonicalMixedBoundaryHeightReadoutResidualCorrection
    mixedBoundaryResidualCorrection mixedBoundaryLeftResidual
    mixedBoundaryRightResidual mixedBoundaryJetLeftResidual
    mixedBoundaryJetRightResidual
  dsimp only
  ring

/-- The four defects extracted from `R` are the same universal polarization
as the camera defects, instantiated with the complete TFVD traces on the left
and the four synthesized leg traces on the right. -/
theorem canonicalC3FiniteMixedHeightPolarizedReadoutResidualState_eq_generic
    (M : ℕ) (z w : ℂ) :
    canonicalC3FiniteMixedHeightPolarizedReadoutResidualState M z w =
      polarizedCrossResidualChannelState
        (canonicalBoundaryResidualData
          M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) z).valueReadout
        (Complex.I * (canonicalBoundaryResidualData
          M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) z).logJetReadout)
        (canonicalBoundaryResidualData
          M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) w).valueReadout
        (Complex.I * (canonicalBoundaryResidualData
          M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) w).logJetReadout)
        (canonicalC3FiniteMixedHeightSynthesizedValueZ M z w)
        (canonicalC3FiniteMixedHeightSynthesizedCompanionZ M z w)
        (canonicalC3FiniteMixedHeightSynthesizedValueW M z w)
        (canonicalC3FiniteMixedHeightSynthesizedCompanionW M z w) := by
  unfold canonicalC3FiniteMixedHeightPolarizedReadoutResidualState
    canonicalC3FiniteMixedHeightZLogResidualChannel
    canonicalC3FiniteMixedHeightWValueResidualChannel
    canonicalC3FiniteMixedHeightZValueResidualChannel
    canonicalC3FiniteMixedHeightWLogResidualChannel
    canonicalC3FiniteMixedHeightSynthesizedValueZ
    canonicalC3FiniteMixedHeightSynthesizedCompanionZ
    canonicalC3FiniteMixedHeightSynthesizedValueW
    canonicalC3FiniteMixedHeightSynthesizedCompanionW
    polarizedCrossResidualChannelState mixedBoundaryLeftResidual
    mixedBoundaryRightResidual mixedBoundaryJetLeftResidual
    mixedBoundaryJetRightResidual
  dsimp only
  simp only [map_sub, map_sum]
  simp

/-- Projection theorem extracting the four camera-shaped defects from the
fully opened structural state. -/
@[simp] theorem canonicalC3FiniteMixedHeightExpandedStructuralState_defects
    (M : ℕ) (z w : ℂ) :
    (canonicalC3FiniteMixedHeightExpandedStructuralState M z w).snd.snd =
      canonicalC3FiniteMixedHeightPolarizedReadoutResidualState M z w := by
  rfl

/-- The expanded readout is exactly `P + O + R`, with `R` obtained only after
the four polarized defects have been retained. -/
theorem canonicalC3MixedExpandedStructuralScalarReadout_state
    (M : ℕ) (z w : ℂ) :
    canonicalC3MixedExpandedStructuralScalarReadout
        (canonicalC3FiniteMixedHeightExpandedStructuralState M z w) =
      canonicalC3FiniteMixedHeightStructuralDefect M z w := by
  change
    canonicalC3FiniteMixedHeightGreenProvenanceChannel M z w +
        canonicalC3FiniteMixedHeightOffDiagonalChannel M z w +
      polarizedCameraCrossResidualChannelScalarReadout
        (canonicalC3FiniteMixedHeightPolarizedReadoutResidualState M z w) = _
  rw [canonicalC3MixedStructuralScalarReadout_polarizedResidualState,
    canonicalC3FiniteMixedHeightStructuralDefect_eq_channelSum]

/-- At the canonical camera itself, the finite cross value residual vanishes
before polarization. -/
@[simp] theorem finiteCameraCrossValueResidual_three
    (cutoff : ℕ) (s : ℂ) :
    finiteCameraCrossValueResidual 3 cutoff s = 0 := by
  simp [finiteCameraCrossValueResidual, finiteCameraCrossLeftValue,
    finiteCameraCrossRightValue]

/-- The corresponding log-jet residual also vanishes before rotation. -/
@[simp] theorem finiteCameraCrossLogJetResidual_three
    (cutoff : ℕ) (s : ℂ) :
    finiteCameraCrossLogJetResidual 3 cutoff s = 0 := by
  have hzero : finiteCameraCrossValueResidual 3 cutoff = (0 : ℂ → ℂ) := by
    funext u
    exact finiteCameraCrossValueResidual_three cutoff u
  unfold finiteCameraCrossLogJetResidual
  rw [hzero]
  simp

/-- Hence all four channels, not merely their scalar sum, vanish when the two
camera sides are both the canonical camera. -/
@[simp] theorem finiteHeightPolarizedCameraCrossResidualChannelState_three
    (cutoff : ℕ) (z w : ℂ) :
    finiteHeightPolarizedCameraCrossResidualChannelState 3 cutoff z w = 0 := by
  simp [finiteHeightPolarizedCameraCrossResidualChannelState,
    finiteHeightPolarizedCameraCrossZLogResidualChannel,
    finiteHeightPolarizedCameraCrossWValueResidualChannel,
    finiteHeightPolarizedCameraCrossZValueResidualChannel,
    finiteHeightPolarizedCameraCrossWLogResidualChannel]

/-- The first telescoping layer is exactly the existing Green-provenance
coordinate. -/
theorem canonicalC3FiniteMixedHeightLocalGreenResidualChannel_eq
    (M : ℕ) (z w : ℂ) :
    canonicalC3FiniteMixedHeightLocalGreenResidualChannel M z w =
      canonicalC3FiniteMixedHeightGreenProvenanceChannel M z w := by
  simpa [canonicalC3FiniteMixedHeightLocalGreenResidualChannel] using
    canonicalC3AllCutoffMixedSourcePrefixState_greenProvenanceReadout_eq
      M z w

/-- The second telescoping layer is exactly the retained ordered
off-diagonal coordinate. -/
theorem canonicalC3FiniteMixedHeightGlobalLocalResidualChannel_eq
    (M : ℕ) (z w : ℂ) :
    canonicalC3FiniteMixedHeightGlobalLocalResidualChannel M z w =
      canonicalC3FiniteMixedHeightOffDiagonalChannel M z w := by
  let state := canonicalC3AllCutoffMixedSourcePrefixState M z w
  let legs := state.mixedLegs M
  have hdecomposition :=
    sameSEdgeBoundaryWedge_sum_eq_local_add_crossProvenance
      legs.left legs.right legs.jetLeft legs.jetRight
  have hlayer :
      sameSEdgeBoundaryWedge
          (∑ i, legs.left i) (∑ i, legs.right i)
          (∑ i, legs.jetLeft i) (∑ i, legs.jetRight i) -
        ∑ i, sameSEdgeBoundaryWedge
          (legs.left i) (legs.right i) (legs.jetLeft i) (legs.jetRight i) =
        twoLegBoundaryCrossProvenance
          legs.left legs.right legs.jetLeft legs.jetRight := by
    linear_combination hdecomposition
  calc
    canonicalC3FiniteMixedHeightGlobalLocalResidualChannel M z w =
        twoLegBoundaryCrossProvenance
          legs.left legs.right legs.jetLeft legs.jetRight := by
      simpa [canonicalC3FiniteMixedHeightGlobalLocalResidualChannel,
        state, legs] using hlayer
    _ = CanonicalC3AllCutoffMixedSourceHilbert.offDiagonalReadout
          M state := by
      rfl
    _ = canonicalC3FiniteMixedHeightOffDiagonalChannel M z w := by
      simpa [state] using
        canonicalC3AllCutoffMixedSourcePrefixState_offDiagonalReadout_eq
          M z w

/-- The third telescoping layer is exactly the retained height-readout
residual coordinate. -/
theorem canonicalC3FiniteMixedHeightHeadGlobalResidualChannel_eq
    (M : ℕ) (z w : ℂ) :
    canonicalC3FiniteMixedHeightHeadGlobalResidualChannel M z w =
      canonicalC3FiniteMixedHeightReadoutResidualChannel M z w := by
  let state := canonicalC3AllCutoffMixedSourcePrefixState M z w
  let legs := state.mixedLegs M
  let valueZ :=
    CanonicalC3AllCutoffMixedSourceHilbert.valueHeadReadout M state.zSource
  let logJetZ :=
    CanonicalC3AllCutoffMixedSourceHilbert.logJetHeadReadout M state.zSource
  let valueW :=
    CanonicalC3AllCutoffMixedSourceHilbert.valueHeadReadout M state.wSource
  let logJetW :=
    CanonicalC3AllCutoffMixedSourceHilbert.logJetHeadReadout M state.wSource
  have hdecomposition :=
    mixedScalarBoundaryWedge_eq_summedTwoLeg_add_residualCorrection
      valueZ (Complex.I * logJetZ) valueW (Complex.I * logJetW) legs
  have hlayer :
      mixedScalarBoundaryWedge
          valueZ (Complex.I * logJetZ) valueW (Complex.I * logJetW) -
        sameSEdgeBoundaryWedge
          (∑ i, legs.left i) (∑ i, legs.right i)
          (∑ i, legs.jetLeft i) (∑ i, legs.jetRight i) =
        mixedBoundaryResidualCorrection
          valueZ (Complex.I * logJetZ) valueW (Complex.I * logJetW) legs := by
    linear_combination hdecomposition
  calc
    canonicalC3FiniteMixedHeightHeadGlobalResidualChannel M z w =
        mixedBoundaryResidualCorrection
          valueZ (Complex.I * logJetZ) valueW (Complex.I * logJetW) legs := by
      simpa [canonicalC3FiniteMixedHeightHeadGlobalResidualChannel,
        state, legs, valueZ, logJetZ, valueW, logJetW] using hlayer
    _ = CanonicalC3AllCutoffMixedSourceHilbert.heightResidualReadout
          M state := by
      rfl
    _ = canonicalC3FiniteMixedHeightReadoutResidualChannel M z w := by
      simpa [state] using
        canonicalC3AllCutoffMixedSourcePrefixState_heightResidualReadout_eq
          M z w

/-- Final vector arrow for the three TFVD/Green telescoping layers.  The proof
uses the three coordinate identities independently; no scalar channel sum is
used. -/
theorem canonicalC3FiniteMixedHeightPolarizedLayerResidualState_eq_structural
    (M : ℕ) (z w : ℂ) :
    canonicalC3FiniteMixedHeightPolarizedLayerResidualState M z w =
      canonicalC3FiniteMixedHeightStructuralChannelState M z w := by
  unfold canonicalC3FiniteMixedHeightPolarizedLayerResidualState
    canonicalC3FiniteMixedHeightStructuralChannelState
  rw [canonicalC3FiniteMixedHeightLocalGreenResidualChannel_eq,
    canonicalC3FiniteMixedHeightGlobalLocalResidualChannel_eq,
    canonicalC3FiniteMixedHeightHeadGlobalResidualChannel_eq]

/-- Only after the vector arrow has been established, the complete endpoint
residual is identified with the previously retained structural defect. -/
theorem canonicalC3FiniteMixedHeightTfvdGreenPolarizedResidual_eq_structuralDefect
    (M : ℕ) (z w : ℂ) :
    canonicalC3FiniteMixedHeightTfvdGreenPolarizedResidual M z w =
      canonicalC3FiniteMixedHeightStructuralDefect M z w := by
  have hdecomposition :=
    canonicalMixedEnrichedHeightScalarBoundary_eq_green_add_explicitDefects
      M tfvdHaarScale_ne_zero (fun _ : ℕ => (1 : ℂ))
        (by intro m; norm_num) z w
  unfold canonicalC3FiniteMixedHeightTfvdGreenPolarizedResidual
    canonicalC3FiniteMixedHeightStructuralDefect
  dsimp only
  linear_combination hdecomposition

/-- Full opening of `P+O+R` into exactly four Hilbert-space polarization
defects.  No structural scalar channel is retained on the left-hand side. -/
theorem canonicalC3FullPolarizedStructuralResidualState_scalarReadout
    (M : ℕ) (z w : ℂ) :
    polarizedCameraCrossResidualChannelScalarReadout
        (canonicalC3FiniteMixedHeightFullPolarizedStructuralResidualState
          M z w) =
      canonicalC3FiniteMixedHeightStructuralDefect M z w := by
  unfold canonicalC3FiniteMixedHeightFullPolarizedStructuralResidualState
  dsimp only
  rw [polarizedCameraCrossResidualChannelScalarReadout_greenFormState,
    greenForm_canonicalC3FiniteMixedHeightScalarBoundaryPair,
    greenForm_canonicalC3FiniteMixedHeightGreenBoundaryPair]
  exact canonicalC3FiniteMixedHeightTfvdGreenPolarizedResidual_eq_structuralDefect
    M z w

/-- Scalar telescoping is now a corollary of the vector equality, rather than
an input to it. -/
theorem canonicalC3MixedStructuralScalarReadout_layerResidualState
    (M : ℕ) (z w : ℂ) :
    canonicalC3MixedStructuralScalarReadout
        (canonicalC3FiniteMixedHeightPolarizedLayerResidualState M z w) =
      canonicalC3FiniteMixedHeightTfvdGreenPolarizedResidual M z w := by
  calc
    canonicalC3MixedStructuralScalarReadout
        (canonicalC3FiniteMixedHeightPolarizedLayerResidualState M z w) =
        canonicalC3MixedStructuralScalarReadout
          (canonicalC3FiniteMixedHeightStructuralChannelState M z w) := by
      rw [canonicalC3FiniteMixedHeightPolarizedLayerResidualState_eq_structural]
    _ = canonicalC3FiniteMixedHeightStructuralDefect M z w :=
      canonicalC3MixedStructuralScalarReadout_state M z w
    _ = canonicalC3FiniteMixedHeightTfvdGreenPolarizedResidual M z w :=
      (canonicalC3FiniteMixedHeightTfvdGreenPolarizedResidual_eq_structuralDefect
        M z w).symm

theorem polarizedCameraCrossResidual_eq_zero
    {camera : ℕ} (hcamera : 2 ≤ camera) {z w : ℂ}
    (hz : z ∈ bracketDomain) (hw : w ∈ bracketDomain) :
    polarizedCameraCrossResidual camera z w = 0 := by
  unfold polarizedCameraCrossResidual
  rw [cameraCrossLeftValue_eq_rightValue hcamera hz,
    cameraCrossLeftLogJet_eq_rightLogJet hcamera hz,
    cameraCrossLeftValue_eq_rightValue hcamera hw,
    cameraCrossLeftLogJet_eq_rightLogJet hcamera hw]
  ring

theorem heightPolarizedCameraCrossResidual_eq_zero
    {camera : ℕ} (hcamera : 2 ≤ camera) {z w : ℂ}
    (hz : z ∈ bracketDomain) (hw : w ∈ bracketDomain) :
    heightPolarizedCameraCrossResidual camera z w = 0 := by
  unfold heightPolarizedCameraCrossResidual
  rw [cameraCrossLeftValue_eq_rightValue hcamera hz,
    cameraCrossLeftLogJet_eq_rightLogJet hcamera hz,
    cameraCrossLeftValue_eq_rightValue hcamera hw,
    cameraCrossLeftLogJet_eq_rightLogJet hcamera hw]
  ring

/-- The four finite polarized camera defects converge jointly to the zero
vector.  Each coordinate is controlled independently before the Hilbert
state is assembled, so this conclusion does not use cancellation in the
scalar readout. -/
theorem finiteHeightPolarizedCameraCrossResidualChannelState_tendsto_zero
    {camera : ℕ} (hcamera : 2 ≤ camera) {z w : ℂ}
    (hz : z ∈ bracketDomain) (hw : w ∈ bracketDomain) :
    Tendsto
      (fun cutoff : ℕ =>
        finiteHeightPolarizedCameraCrossResidualChannelState
          camera cutoff z w)
      atTop (nhds 0) := by
  have hzValueResidual :=
    finiteCameraCrossValueResidual_tendsto_zero hcamera hz
  have hwValueResidual :=
    finiteCameraCrossValueResidual_tendsto_zero hcamera hw
  have hzLogResidual :=
    finiteCameraCrossLogJetResidual_tendsto_zero hcamera hz
  have hwLogResidual :=
    finiteCameraCrossLogJetResidual_tendsto_zero hcamera hw
  have hzRightValue := finiteCameraCrossRightValue_tendsto hcamera hz
  have hwLeftValue := finiteCameraCrossLeftValue_tendsto hcamera hw
  have hzRightLogJet := finiteCameraCrossRightLogJet_tendsto hcamera hz
  have hwLeftLogJet := finiteCameraCrossLeftLogJet_tendsto hcamera hw
  have hfirst : Tendsto
      (fun cutoff : ℕ =>
        finiteHeightPolarizedCameraCrossZLogResidualChannel
          camera cutoff z w) atTop (nhds 0) := by
    simpa [finiteHeightPolarizedCameraCrossZLogResidualChannel] using
      (hzLogResidual.const_mul Complex.I).mul hwLeftValue.star
  have hsecond : Tendsto
      (fun cutoff : ℕ =>
        finiteHeightPolarizedCameraCrossWValueResidualChannel
          camera cutoff z w) atTop (nhds 0) := by
    simpa [finiteHeightPolarizedCameraCrossWValueResidualChannel] using
      (hzRightLogJet.const_mul Complex.I).mul hwValueResidual.star
  have hthird : Tendsto
      (fun cutoff : ℕ =>
        finiteHeightPolarizedCameraCrossZValueResidualChannel
          camera cutoff z w) atTop (nhds 0) := by
    simpa [finiteHeightPolarizedCameraCrossZValueResidualChannel] using
      (hzValueResidual.mul
        (hwLeftLogJet.const_mul Complex.I).star).neg
  have hfourth : Tendsto
      (fun cutoff : ℕ =>
        finiteHeightPolarizedCameraCrossWLogResidualChannel
          camera cutoff z w) atTop (nhds 0) := by
    simpa [finiteHeightPolarizedCameraCrossWLogResidualChannel] using
      (hzRightValue.mul
        (hwLogResidual.const_mul Complex.I).star).neg
  have hthirdFourth := hthird.prodMk_nhds hfourth
  have hthirdFourthLp :=
    (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp
      hthirdFourth
  have hsecondRest := hsecond.prodMk_nhds hthirdFourthLp
  have hsecondRestLp :=
    (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp
      hsecondRest
  have hall := hfirst.prodMk_nhds hsecondRestLp
  have hallLp :=
    (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp hall
  unfold finiteHeightPolarizedCameraCrossResidualChannelState
  convert hallLp using 1
  · simp [Function.comp_def]
  · rfl

theorem finitePolarizedCameraCrossResidual_tendsto_zero
    {camera : ℕ} (hcamera : 2 ≤ camera) {z w : ℂ}
    (hz : z ∈ bracketDomain) (hw : w ∈ bracketDomain) :
    Tendsto (fun cutoff : ℕ =>
      finitePolarizedCameraCrossResidual camera cutoff z w)
      atTop (nhds 0) := by
  have hzLeftValue := finiteCameraCrossLeftValue_tendsto hcamera hz
  have hzLeftLogJet := finiteCameraCrossLeftLogJet_tendsto hcamera hz
  have hwLeftValue := finiteCameraCrossLeftValue_tendsto hcamera hw
  have hwLeftLogJet := finiteCameraCrossLeftLogJet_tendsto hcamera hw
  have hzRightValue := finiteCameraCrossRightValue_tendsto hcamera hz
  have hzRightLogJet := finiteCameraCrossRightLogJet_tendsto hcamera hz
  have hwRightValue := finiteCameraCrossRightValue_tendsto hcamera hw
  have hwRightLogJet := finiteCameraCrossRightLogJet_tendsto hcamera hw
  have hleft :=
    (hzLeftLogJet.mul hwLeftValue.star).sub
      (hzLeftValue.mul hwLeftLogJet.star)
  have hright :=
    (hzRightLogJet.mul hwRightValue.star).sub
      (hzRightValue.mul hwRightLogJet.star)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      finitePolarizedCameraCrossResidual camera cutoff z w)
      atTop (nhds (polarizedCameraCrossResidual camera z w)) := by
    simpa [finitePolarizedCameraCrossResidual,
      polarizedCameraCrossResidual, mixedScalarBoundaryWedge] using
        hleft.sub hright
  simpa only [polarizedCameraCrossResidual_eq_zero hcamera hz hw] using hlimit

theorem finiteHeightPolarizedCameraCrossResidual_tendsto_zero
    {camera : ℕ} (hcamera : 2 ≤ camera) {z w : ℂ}
    (hz : z ∈ bracketDomain) (hw : w ∈ bracketDomain) :
    Tendsto (fun cutoff : ℕ =>
      finiteHeightPolarizedCameraCrossResidual camera cutoff z w)
      atTop (nhds 0) := by
  have hzLeftValue := finiteCameraCrossLeftValue_tendsto hcamera hz
  have hzLeftLogJet :=
    (finiteCameraCrossLeftLogJet_tendsto hcamera hz).const_mul Complex.I
  have hwLeftValue := finiteCameraCrossLeftValue_tendsto hcamera hw
  have hwLeftLogJet :=
    (finiteCameraCrossLeftLogJet_tendsto hcamera hw).const_mul Complex.I
  have hzRightValue := finiteCameraCrossRightValue_tendsto hcamera hz
  have hzRightLogJet :=
    (finiteCameraCrossRightLogJet_tendsto hcamera hz).const_mul Complex.I
  have hwRightValue := finiteCameraCrossRightValue_tendsto hcamera hw
  have hwRightLogJet :=
    (finiteCameraCrossRightLogJet_tendsto hcamera hw).const_mul Complex.I
  have hleft :=
    (hzLeftLogJet.mul hwLeftValue.star).sub
      (hzLeftValue.mul hwLeftLogJet.star)
  have hright :=
    (hzRightLogJet.mul hwRightValue.star).sub
      (hzRightValue.mul hwRightLogJet.star)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      finiteHeightPolarizedCameraCrossResidual camera cutoff z w)
      atTop (nhds (heightPolarizedCameraCrossResidual camera z w)) := by
    simpa [finiteHeightPolarizedCameraCrossResidual,
      heightPolarizedCameraCrossResidual, mixedScalarBoundaryWedge] using
        hleft.sub hright
  simpa only [heightPolarizedCameraCrossResidual_eq_zero hcamera hz hw] using hlimit

/-- The canonical height-coordinate residual tends to zero throughout the
product critical strip. -/
theorem canonicalC3FiniteHeightPolarizedCameraCrossResidual_tendsto_zero
    {camera : ℕ} (hcamera : 2 ≤ camera) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    Tendsto (fun cutoff : ℕ =>
      canonicalC3FiniteHeightPolarizedCameraCrossResidual
        camera cutoff z w) atTop (nhds 0) := by
  have hzDomain : operatorHeightParameter z ∈ bracketDomain := by
    change -1 < (operatorHeightParameter z).re
    linarith [hz.1]
  have hwDomain : operatorHeightParameter w ∈ bracketDomain := by
    change -1 < (operatorHeightParameter w).re
    linarith [hw.1]
  simpa only [canonicalC3FiniteHeightPolarizedCameraCrossResidual] using
    finiteHeightPolarizedCameraCrossResidual_tendsto_zero
      hcamera hzDomain hwDomain


end

end CarrySelfAdjointOperator
