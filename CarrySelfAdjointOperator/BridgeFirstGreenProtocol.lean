import CarrySelfAdjointOperator.CanonicalC3StripScalarization
import CarrySelfAdjointOperator.CanonicalC3GammaEnergyNormalization
import CarrySelfAdjointOperator.CompletedTfvdCanonicalSourceIntertwining
import NativeCarryC3Crosswalk.EnrichedTfvdPairTailClosure

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Infinite

noncomputable section

abbrev CanonicalCompletedC3ValueLogJetCarrier (s : ℂ) :
    NativeCarryC3Crosswalk.CompletedTfvdGreenLedger :=
  NativeCarryC3Crosswalk.seededCompletedTfvdGreenLedger 1 s

theorem canonicalCompletedC3ValueCarrier_eq
    (s : ℂ) :
    (CanonicalCompletedC3ValueLogJetCarrier s).1.1 =
        nativeGpreTfvdSameEdgeGlue
        nativeGpreCanonicalVerticalRealization
        (c2DirichletGradientPrefixCore s 3) := by
  simp [CanonicalCompletedC3ValueLogJetCarrier]

theorem canonicalCompletedC3LogJetCarrier_eq
    (s : ℂ) :
    (CanonicalCompletedC3ValueLogJetCarrier s).1.2 =
        nativeGpreTfvdSameEdgeGlue
        nativeGpreCanonicalVerticalRealization
        (c2LogJetPrefixCore s 3) := by
  simp [CanonicalCompletedC3ValueLogJetCarrier]

theorem canonicalCompletedC3GreenFormBridge
    (s : ℂ) :
    NativeCarryC3Crosswalk.completedTfvdGreenLedgerSameSBoundary
          (CanonicalCompletedC3ValueLogJetCarrier s) -
        finiteCanonicalTfvdSameSGreenProvenanceDefect 3 1 s =
      greenForm
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3 s)
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
          3 (reflectedParameter s)) := by
  simpa [CanonicalCompletedC3ValueLogJetCarrier] using
    NativeCarryC3Crosswalk.completedTfvdGreenLedgerSameSBoundary_sub_provenance_eq_greenForm s

theorem canonicalCompletedC3GreenPortCarrier_eq
    (s : ℂ) :
    NativeCarryC3Crosswalk.completedTfvdGreenLedgerC3Port s
        (CanonicalCompletedC3ValueLogJetCarrier s) =
      NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3 s := by
  simpa [CanonicalCompletedC3ValueLogJetCarrier] using
    NativeCarryC3Crosswalk.completedTfvdGreenLedgerC3Port_seeded s

theorem canonicalCompletedC3SourceCarrier_eq
    (z : ℂ) :
    canonicalCompletedC3SixCameraSource z =
      NativeCarryC3Crosswalk.seededCompletedTfvdGreenCameraState
        (operatorHeightParameter z) :=
  canonicalCompletedC3SixCameraSource_eq_completedTfvdGreenCameraState z

abbrev CanonicalCompletedC3EnrichedTfvdPair (s : ℂ) :
    NativeCarryC3Crosswalk.EnrichedTfvdValueLogJetPair :=
  NativeCarryC3Crosswalk.canonicalEnrichedTfvdValueLogJetPair
    tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) s

abbrev CanonicalCompletedC3EnrichedTfvdTransport (s : ℂ) :
    NativeCarryC3Crosswalk.FiniteC3EnrichedTfvdPairTransportData 1 :=
  NativeCarryC3Crosswalk.finiteC3EnrichedTfvdPairTransport
    1 tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) s
    (CanonicalCompletedC3EnrichedTfvdPair s)

theorem canonicalCompletedC3EnrichedTfvdTransport_components
    (s : ℂ) :
    let data := CanonicalCompletedC3EnrichedTfvdTransport s
    (data.valueReadout = finiteBracketedDirichletChart 3 1 s) ∧
    (data.logJetReadout = finiteCanonicalLogBracketChart 1 s) ∧
    (data.greenPort =
      NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3 s) := by
  simpa [CanonicalCompletedC3EnrichedTfvdTransport,
    CanonicalCompletedC3EnrichedTfvdPair] using
    (NativeCarryC3Crosswalk.finiteC3EnrichedTfvdPairTransport_canonical
      1 tfvdHaarScale_ne_zero (fun _ : ℕ => (1 : ℂ))
      (by intro m; norm_num) s)

theorem canonicalCompletedC3EnrichedTfvdCorrectedBoundary_eq_greenForm
    (s : ℂ) :
    NativeCarryC3Crosswalk.finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary
        1 tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) s =
      greenForm
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3 s)
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
          3 (reflectedParameter s)) := by
  simpa using
    (NativeCarryC3Crosswalk.finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary_eq_greenForm
      1 tfvdHaarScale_ne_zero (fun _ : ℕ => (1 : ℂ))
      (by intro m; norm_num) s)

theorem canonicalCompletedC3EnrichedTfvdTailReadout_eq_genuine
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    NativeCarryC3Crosswalk.finiteC3CanonicalEnrichedTfvdPairTailReadout
        1 tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) s =
      cpChartFactor 3 s * genuineContinuation s := by
  exact
    NativeCarryC3Crosswalk.finiteC3CanonicalEnrichedTfvdPairTailReadout_eq_factor_mul_genuine
      1 tfvdHaarScale_ne_zero (fun _ : ℕ => (1 : ℂ))
      (by intro m; norm_num) hs

theorem canonicalCompletedC3EnrichedTfvdTailReadout_eq_nativeScalar
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    NativeCarryC3Crosswalk.finiteC3CanonicalEnrichedTfvdPairTailReadout
        1 tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) s =
      cpChartFactor 3 s * nativeScalar s := by
  rw [canonicalCompletedC3EnrichedTfvdTailReadout_eq_genuine hs,
    nativeScalar_eq_genuineContinuation hs]

theorem nativeXi_mul_enrichedTfvdTailReadout_eq_completedCharacteristic
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    nativeXiCompletionFactor (centeredHeightParameter s) *
        NativeCarryC3Crosswalk.finiteC3CanonicalEnrichedTfvdPairTailReadout
          1 tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) s =
      cpChartFactor 3 s *
        completedNativeOperatorCharacteristic (centeredHeightParameter s) := by
  rw [canonicalCompletedC3EnrichedTfvdTailReadout_eq_nativeScalar hs]
  unfold completedNativeOperatorCharacteristic
  rw [operatorHeightParameter_centeredHeightParameter]
  ring

theorem canonicalCompletedC3EnrichedTfvdTailDefect_eq_zero_iff_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    NativeCarryC3Crosswalk.finiteC3EnrichedTfvdPairTailDefect
        1 tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) s = 0 ↔
      genuineContinuation s = 0 := by
  exact
    NativeCarryC3Crosswalk.finiteC3EnrichedTfvdPairTailDefect_eq_zero_iff_genuine_zero
      1 tfvdHaarScale_ne_zero (fun _ : ℕ => (1 : ℂ))
      (by intro m; norm_num) hs

theorem canonicalCompletedC3EnrichedTfvdCorrectedBoundaryCloses_iff_re_eq_half
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    NativeCarryC3Crosswalk.C3EnrichedTfvdCorrectedPairBoundaryClosesAt
        tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) s ↔
      s.re = (1 : ℝ) / 2 := by
  exact
    NativeCarryC3Crosswalk.c3EnrichedTfvdCorrectedPairBoundaryClosesAt_iff_re_eq_half
      tfvdHaarScale_ne_zero (fun _ : ℕ => (1 : ℂ))
      (by intro m; norm_num) hs

abbrev CanonicalCompletedC3TransportedGammaState
    (s : ℂ) (hoff : s.re ≠ (1 : ℝ) / 2) :
    RealifiedNaimarkComplexification :=
  NativeCarryC3Crosswalk.seededCompletedTfvdCarryGammaState s hoff

def canonicalCompletedC3TransportedGammaEnergy
    (s : ℂ) (hoff : s.re ≠ (1 : ℝ) / 2) : ℝ :=
  ‖(CanonicalCompletedC3TransportedGammaState s hoff).fst‖ ^ 2 +
    ‖(CanonicalCompletedC3TransportedGammaState s hoff).snd‖ ^ 2

def canonicalCompletedC3TransportedBoundaryGreenForm
    (s : ℂ) (hoff : s.re ≠ (1 : ℝ) / 2) : ℝ :=
  let z := carryComplexTimeOfParameter s
  let hz :=
    NativeCarryC3Crosswalk.carryComplexTimeOfParameter_im_ne_zero_of_re_ne_half hoff
  let u := NativeCarryC3Crosswalk.seededCompletedTfvdGreenCameraState s
  greenForm (𝕜 := ℝ)
      ((allBasesCauchyBlock z hz u).snd, u.snd)
      ((allBasesCauchyBlock z hz u).fst, u.fst) -
    greenForm (𝕜 := ℝ)
      ((allBasesCauchyBlock z hz u).fst, u.fst)
      ((allBasesCauchyBlock z hz u).snd, u.snd)

theorem canonicalCompletedC3TransportedGreenForm_eq_normSq
    (s : ℂ) (hoff : s.re ≠ (1 : ℝ) / 2) :
    canonicalCompletedC3TransportedBoundaryGreenForm s hoff =
      2 * (carryComplexTimeOfParameter s).im *
        canonicalCompletedC3TransportedGammaEnergy s hoff := by
  simpa [canonicalCompletedC3TransportedBoundaryGreenForm,
    canonicalCompletedC3TransportedGammaEnergy,
    CanonicalCompletedC3TransportedGammaState] using
    (NativeCarryC3Crosswalk.seededCompletedTfvdCarryGammaState_diagonal_green_identity
      (s := s) hoff).symm

theorem canonicalCompletedC3TransportedGammaEnergy_pos
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    0 < canonicalCompletedC3TransportedGammaEnergy s hoff := by
  exact NativeCarryC3Crosswalk.seededCompletedTfvdCarryGammaEnergy_pos hs hoff

structure CanonicalCompletedC3BridgeFirstData : Prop where
  valueCarrier :
    ∀ s : ℂ,
      (CanonicalCompletedC3ValueLogJetCarrier s).1.1 =
        nativeGpreTfvdSameEdgeGlue
          nativeGpreCanonicalVerticalRealization
          (c2DirichletGradientPrefixCore s 3)
  logJetCarrier :
    ∀ s : ℂ,
      (CanonicalCompletedC3ValueLogJetCarrier s).1.2 =
        nativeGpreTfvdSameEdgeGlue
          nativeGpreCanonicalVerticalRealization
          (c2LogJetPrefixCore s 3)
  greenFormBridge :
    ∀ s : ℂ,
      NativeCarryC3Crosswalk.completedTfvdGreenLedgerSameSBoundary
            (CanonicalCompletedC3ValueLogJetCarrier s) -
          finiteCanonicalTfvdSameSGreenProvenanceDefect 3 1 s =
        greenForm
          (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3 s)
          (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
            3 (reflectedParameter s))
  greenPortCarrier :
    ∀ s : ℂ,
      NativeCarryC3Crosswalk.completedTfvdGreenLedgerC3Port s
          (CanonicalCompletedC3ValueLogJetCarrier s) =
        NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3 s
  sourceCarrier :
    ∀ z : ℂ,
      canonicalCompletedC3SixCameraSource z =
        NativeCarryC3Crosswalk.seededCompletedTfvdGreenCameraState
          (operatorHeightParameter z)
  enrichedTransport :
    ∀ s : ℂ,
      let data := CanonicalCompletedC3EnrichedTfvdTransport s
      (data.valueReadout = finiteBracketedDirichletChart 3 1 s) ∧
      (data.logJetReadout = finiteCanonicalLogBracketChart 1 s) ∧
      (data.greenPort =
        NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3 s)
  enrichedCorrectedBoundary :
    ∀ s : ℂ,
      NativeCarryC3Crosswalk.finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary
          1 tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) s =
        greenForm
          (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3 s)
          (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
            3 (reflectedParameter s))
  enrichedTailReadout :
    ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
      NativeCarryC3Crosswalk.finiteC3CanonicalEnrichedTfvdPairTailReadout
          1 tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) s =
        cpChartFactor 3 s * genuineContinuation s
  completedValueBridge :
    ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
      nativeXiCompletionFactor (centeredHeightParameter s) *
          NativeCarryC3Crosswalk.finiteC3CanonicalEnrichedTfvdPairTailReadout
            1 tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) s =
        cpChartFactor 3 s *
          completedNativeOperatorCharacteristic (centeredHeightParameter s)

theorem canonicalCompletedC3BridgeFirstData_proved :
    CanonicalCompletedC3BridgeFirstData where
  valueCarrier := canonicalCompletedC3ValueCarrier_eq
  logJetCarrier := canonicalCompletedC3LogJetCarrier_eq
  greenFormBridge := canonicalCompletedC3GreenFormBridge
  greenPortCarrier := canonicalCompletedC3GreenPortCarrier_eq
  sourceCarrier := canonicalCompletedC3SourceCarrier_eq
  enrichedTransport := canonicalCompletedC3EnrichedTfvdTransport_components
  enrichedCorrectedBoundary :=
    canonicalCompletedC3EnrichedTfvdCorrectedBoundary_eq_greenForm
  enrichedTailReadout := canonicalCompletedC3EnrichedTfvdTailReadout_eq_genuine
  completedValueBridge :=
    nativeXi_mul_enrichedTfvdTailReadout_eq_completedCharacteristic

theorem canonicalCompletedC3Energy_after_bridge
    (_hbridge : CanonicalCompletedC3BridgeFirstData)
    (hscalar : CanonicalCompletedC3GammaCauchyStripScalarization) :
    CanonicalCompletedC3GammaStripDiagonalEnergy :=
  canonicalCompletedC3GammaCauchyStripScalarization_iff_energy.mp
    hscalar

theorem finalGenuineZeroConfinement_of_bridgeFirstScalarization
    (_hbridge : CanonicalCompletedC3BridgeFirstData)
    (hscalar : CanonicalCompletedC3GammaCauchyStripScalarization) :
    NativeCarryC3Crosswalk.FinalGenuineZeroConfinement :=
  finalGenuineZeroConfinement_of_canonicalCompletedC3StripScalarization
    hscalar

end

end CarrySelfAdjointOperator
