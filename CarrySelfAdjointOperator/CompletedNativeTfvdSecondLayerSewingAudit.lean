import CarrySelfAdjointOperator.CompletedNativeTfvdSixChannelJet
import CarrySelfAdjointOperator.CompletedNativeRadialHerglotzTwoPoint
import CarrySelfAdjointOperator.CompletedC3FourCornerTaylorGram
import CarrySelfAdjointOperator.CompletedC3ConcreteDressedLowOrderAudit
import CarrySelfAdjointOperator.CompletedNativeHerglotzFourthOrderGate
import CarrySelfAdjointOperator.CompletedC3WronskianResolventRealizationProbe
import Mathlib.Tactic

/-!
# Low-order audit of the second TFVD layer

This module deliberately stops at the first odd layer.  It distinguishes the
strictly positive raw TFVD diagonal from the corrected six-channel third
variation before asking for any cross-carrier sewing.

* `A` is the real diagonal energy of `RawJet 1`.
* `B` is the order-three coefficient of the reconstructed six-analysis TFVD
  functional.
* `C` is the completed normalized-response Taylor coefficient of order three.
* `D` is the native logarithmic moment `h₁`.

The established geometric chain proves `B = C = D`.  The only new question is
the explicitly named residual `A - B`.  In particular, positivity of `A` is
not silently transferred to `B`.

The concrete three-channel dressed carrier does not introduce a new
first-odd energy: its retained residual coordinate is provably flat at this
order, and the ordinary/logarithmic carrier embeds isometrically.  Thus the
same residual can equivalently be read as *dressed positive first-odd energy
minus corrected signed six-channel third variation*.  This removes the
retained residual ray as a possible hidden normalization at this order, but
does not identify a positive Hilbert Gram with the signed Wronskian readout.

The raw all-order bridge does retain a response-plus-raw-return decomposition,
but no available theorem transports that raw return into the corrected
two-port Green boundary
`canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary`.  That unsewn boundary
is the first additional operation in the comparison: it pairs the
reconstructed direct and reflected TFVD ports.  The full six-channel
functional then retains the structural provenance/off-diagonal/readout-
residual triple, tail completion, xi weight, and archimedean chart.  This
audit does not collapse those terms into a new metric or a fitted weight.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- `A`: the positive first-odd diagonal of the raw enriched TFVD Taylor
carrier.  This carrier has exactly an ordinary vertical Taylor coordinate and
its orthogonal logarithmic Taylor coordinate. -/
def canonicalCompletedNativeTfvdFirstOddRawDiagonal : ℝ :=
  (inner ℂ
    (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 1)
    (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 1)).re

/-- The same first-odd energy after the canonical isometric inclusion into
the concrete dressed positive carrier.  Its residual coordinate is zero by
the independently proved first-order residual flatness. -/
def canonicalCompletedNativeTfvdDressedFirstOddDiagonal : ℝ :=
  (inner ℂ
    canonicalCompletedC3DressedFirstOddCoefficientJet
    canonicalCompletedC3DressedFirstOddCoefficientJet).re

/-- `B`: the corrected third variation read only after the six TFVD analyses
have been reconstructed into the all-channel causal/chiral functional. -/
def canonicalCompletedNativeTfvdCorrectedThirdVariation
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) : ℝ :=
  (canonicalC3BracketTfvdSixAnalysisJetCoefficient M 2 q hq0 hq1 S).re

/-- The corrected third variation is the actual third central jet of the
complete six-analysis final readout.  In particular, the expression being
compared with the raw positive diagonal still contains the Green pairing of
the direct/reflected ports, the structural provenance/off-diagonal/readout
coordinates, tail completion, completion weight, and archimedean chart; it
is not a derivative of the raw vertical trace. -/
theorem canonicalCompletedNativeTfvdCorrectedThirdVariation_eq_fullSixChannelFinalReadoutJet
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalCompletedNativeTfvdCorrectedThirdVariation M q hqpos.le hq1 S =
      (iteratedDeriv 3
        (fun z : ℂ =>
          canonicalC3AllCutoffMixedSourceTfvdFinalReadout (M + 1) z 0
              q hqpos.le hq1 S
              (canonicalC3AllCutoffMixedSourceTfvdAnalysis q S
                (canonicalC3AllCutoffMixedSourcePrefixState (M + 1)
                  (operatorHeightParameter z) (operatorHeightParameter 0))) /
            (mixedHermitianWeight canonicalC3ChartFactorHeight z 0 *
              ((2 : ℂ) * completedNativeOperatorCharacteristic z *
                (starRingEnd ℂ) (completedNativeOperatorCharacteristic 0)))) 0 /
        (3 : ℕ).factorial).re := by
  rfl

/-- `C`: the third Taylor coefficient of the completed normalized response. -/
def canonicalCompletedNativeCompletedResponseThirdCoefficient : ℝ :=
  (completedNativeGreenResponseTaylorCoefficient 3).re

/-- `D`: the analytic fourth-order discriminant moment. -/
def canonicalCompletedNativeSecondLayerMoment : ℝ :=
  canonicalCompletedNativeLogDerivativeMoment 1

/-- The raw first-odd diagonal is geometrically positive, before any moment
identification. -/
theorem canonicalCompletedNativeTfvdFirstOddRawDiagonal_pos :
    0 < canonicalCompletedNativeTfvdFirstOddRawDiagonal := by
  exact canonicalCompletedNativeTfvdFirstOddDiagonal_pos

/-- At the first odd layer, the concrete dressed positive carrier preserves
the raw enriched TFVD energy exactly.  Hence the retained residual ray is not
the missing term in the second-layer scalar sewing residual. -/
theorem canonicalCompletedNativeTfvdDressedFirstOddDiagonal_eq_raw :
    canonicalCompletedNativeTfvdDressedFirstOddDiagonal =
      canonicalCompletedNativeTfvdFirstOddRawDiagonal := by
  unfold canonicalCompletedNativeTfvdDressedFirstOddDiagonal
    canonicalCompletedNativeTfvdFirstOddRawDiagonal
  rw [inner_canonicalCompletedC3DressedFirstOddCoefficientJet]

/-- The dressed first-odd diagonal is positive for the same geometric reason
as the raw enriched TFVD diagonal, now with the residual-coordinate flatness
made explicit. -/
theorem canonicalCompletedNativeTfvdDressedFirstOddDiagonal_pos :
    0 < canonicalCompletedNativeTfvdDressedFirstOddDiagonal := by
  rw [canonicalCompletedNativeTfvdDressedFirstOddDiagonal_eq_raw]
  exact canonicalCompletedNativeTfvdFirstOddRawDiagonal_pos

/-- The isometric ordinary/logarithmic inclusion used at the first odd layer
is not a global identification with the actual three-channel dressed state:
already at the center the latter has a strictly positive retained residual
coordinate.  Thus first-odd residual flatness cannot be promoted to an
all-order same-state transport. -/
theorem canonicalCompletedC3RealAxisPositiveState_zero_ne_enrichedTaylorImage :
    canonicalCompletedC3RealAxisPositiveState 0 ≠
      canonicalCompletedC3EnrichedTaylorToPositiveCarrier
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0) := by
  intro hstate
  have hinner := congrArg (fun state : CanonicalCompletedC3RealAxisPositiveCarrier =>
    (inner ℂ state state).re) hstate
  change (canonicalCompletedC3RealAxisPositiveKernel 0 0).re =
      (inner ℂ
        (canonicalCompletedC3EnrichedTaylorToPositiveCarrier
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0))
        (canonicalCompletedC3EnrichedTaylorToPositiveCarrier
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0))).re at hinner
  rw [canonicalCompletedC3EnrichedTaylorToPositiveCarrier_inner] at hinner
  exact (ne_of_gt canonicalCompletedC3RealAxisPositiveKernel_zero_zero_re_gt_enriched) hinner

/-- The raw energy opened in its actual two orthogonal Taylor channels.  In
particular, `RawJet 1` contains the order-one ordinary state and the shifted
order-two state forced by its log jet; it is not a six-channel boundary
state. -/
theorem canonicalCompletedNativeTfvdFirstOddRawDiagonal_eq_rawTaylorChannels :
    canonicalCompletedNativeTfvdFirstOddRawDiagonal =
      (inner ℂ
        (canonicalCompletedNativeTfvdTaylorCoefficientState 1)
        (canonicalCompletedNativeTfvdTaylorCoefficientState 1)).re +
      4 *
        (inner ℂ
          (canonicalCompletedNativeTfvdTaylorCoefficientState 2)
          (canonicalCompletedNativeTfvdTaylorCoefficientState 2)).re := by
  unfold canonicalCompletedNativeTfvdFirstOddRawDiagonal
  rw [inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet_eq_fourCorner]
  norm_num

/-- A carrier-level obstruction to a naive raw-to-corrected transport.  The
direct TFVD Naimark source is a legitimate domain vector, but applying the
resolvent defect operator to it produces a source different from the canonical
six-camera source.  Thus the raw source cannot simply be declared to be the
corrected Green/resolvent state.  This does not, by itself, decide the scalar
first-odd residual below. -/
theorem canonicalCompletedNativeTfvdRawDirectNaimarkSource_inducedDefect_ne_correctedSource
    {z : ℂ} (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hz : z.im ≠ 0) :
    canonicalCompletedC3TfvdNaimarkInducedDefectSource z ≠
      NativeCarrySpectralWeyl.Infinite.realifiedNaimarkPort
        (canonicalCompletedC3SixCameraSource z) := by
  exact canonicalCompletedC3TfvdNaimarkInducedDefectSource_ne_canonical hzStrip hz

/-- The reconstructed six-analysis order-three jet is already the corrected
coefficient, prior to moment recognition. -/
theorem canonicalCompletedNativeTfvdCorrectedThirdVariation_eq_correctedCoefficient
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalCompletedNativeTfvdCorrectedThirdVariation M q hqpos.le hq1 S =
      (canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M 2).re := by
  unfold canonicalCompletedNativeTfvdCorrectedThirdVariation
  rw [canonicalC3BracketTfvdSixAnalysisJet_two M q hqpos hq1 S]

/-- Before the response/moment crosswalk, the corrected third variation is
already the third coefficient of the signed positive-minus-negative chiral
Wronskian balance.  This locates the exact place at which a positive dressed
diagonal would still need a separate polarization sewing theorem. -/
theorem canonicalCompletedNativeTfvdCorrectedThirdVariation_eq_signedChiralThirdVariation
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalCompletedNativeTfvdCorrectedThirdVariation M q hqpos.le hq1 S =
      (canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M 3).re := by
  rw [canonicalCompletedNativeTfvdCorrectedThirdVariation_eq_correctedCoefficient
    M q hqpos hq1 S]
  rfl

/-- The same corrected third variation, with the signed chiral readout
opened into its literal positive-minus-negative Wronskian kernels.  This is
an identity of the completed response, not a positivity inference from either
kernel. -/
theorem canonicalCompletedNativeTfvdCorrectedThirdVariation_eq_fullWronskianChiralBalanceThirdJet
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalCompletedNativeTfvdCorrectedThirdVariation M q hqpos.le hq1 S =
      (iteratedDeriv 3
        (fun z : ℂ => Complex.I *
          (canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel M 0 z -
            canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel M 0 z)) 0 /
        (3 : ℕ).factorial).re := by
  rw [canonicalCompletedNativeTfvdCorrectedThirdVariation_eq_signedChiralThirdVariation
    M q hqpos hq1 S]
  rfl

/-- `B = C`: the corrected six-analysis jet is the third completed response
coefficient.  This is the ports-to-readout statement, not a positivity
argument. -/
theorem canonicalCompletedNativeTfvdCorrectedThirdVariation_eq_completedResponseCoefficient
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalCompletedNativeTfvdCorrectedThirdVariation M q hqpos.le hq1 S =
      canonicalCompletedNativeCompletedResponseThirdCoefficient := by
  unfold canonicalCompletedNativeTfvdCorrectedThirdVariation
    canonicalCompletedNativeCompletedResponseThirdCoefficient
  unfold canonicalC3BracketTfvdSixAnalysisJetCoefficient
  rw [canonicalC3BracketTfvdSixAnalysisNormalizedResponse_eq_sixChannel
    M q hqpos hq1 S]
  have hresponse :
      canonicalC3BracketTfvdSixChannelNormalizedResponse M =ᶠ[nhds 0]
        completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion :=
      (canonicalC3BracketTfvdSixChannelNormalizedResponse_eventuallyEq_response M).trans
      (canonicalC3BracketTfvdNormalizedResponse_eventuallyEq_completed M)
  rw [Filter.EventuallyEq.iteratedDeriv_eq 3 hresponse]
  unfold completedNativeGreenResponseTaylorCoefficient
  norm_num

/-- `C = D`: the third completed-response coefficient is the first new
native moment. -/
theorem canonicalCompletedNativeCompletedResponseThirdCoefficient_eq_moment_one :
    canonicalCompletedNativeCompletedResponseThirdCoefficient =
      canonicalCompletedNativeSecondLayerMoment := by
  unfold canonicalCompletedNativeCompletedResponseThirdCoefficient
    canonicalCompletedNativeSecondLayerMoment
  rw [completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical 1]
  rfl

/-- Consequently `B = C = D`, entirely through the corrected six-channel
readout and before any raw-energy comparison. -/
theorem canonicalCompletedNativeTfvdCorrectedThirdVariation_eq_moment_one
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalCompletedNativeTfvdCorrectedThirdVariation M q hqpos.le hq1 S =
      canonicalCompletedNativeSecondLayerMoment := by
  rw [canonicalCompletedNativeTfvdCorrectedThirdVariation_eq_completedResponseCoefficient
      M q hqpos hq1 S,
    canonicalCompletedNativeCompletedResponseThirdCoefficient_eq_moment_one]

/-- The exact cross-carrier sewing residual.  It is intentionally not set to
zero: doing so is precisely the unproved raw-first-odd identification. -/
def canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) : ℝ :=
  canonicalCompletedNativeTfvdFirstOddRawDiagonal -
    canonicalCompletedNativeTfvdCorrectedThirdVariation M q hq0 hq1 S

/-- The residual with the raw side fully opened.  This is the exact
low-order comparison requested by the audit: raw ordinary/log energy minus
the corrected bracket/six-channel third variation. -/
theorem canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual_eq
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual
        M q hqpos.le hq1 S =
      ((inner ℂ
          (canonicalCompletedNativeTfvdTaylorCoefficientState 1)
          (canonicalCompletedNativeTfvdTaylorCoefficientState 1)).re +
        4 *
          (inner ℂ
            (canonicalCompletedNativeTfvdTaylorCoefficientState 2)
            (canonicalCompletedNativeTfvdTaylorCoefficientState 2)).re) -
        canonicalCompletedNativeTfvdCorrectedThirdVariation M q hqpos.le hq1 S := by
  unfold canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual
  rw [canonicalCompletedNativeTfvdFirstOddRawDiagonal_eq_rawTaylorChannels]

/-- The residual with both sides opened at their actual low-order sources:
the two raw Taylor-channel norms minus the third central jet of the complete
six-analysis final readout.  Thus no unrecorded scalar normalization lies
between `A` and `B`. -/
theorem canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual_eq_rawTaylorChannels_sub_fullSixChannelFinalReadoutJet
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual
        M q hqpos.le hq1 S =
      ((inner ℂ
          (canonicalCompletedNativeTfvdTaylorCoefficientState 1)
          (canonicalCompletedNativeTfvdTaylorCoefficientState 1)).re +
        4 *
          (inner ℂ
            (canonicalCompletedNativeTfvdTaylorCoefficientState 2)
            (canonicalCompletedNativeTfvdTaylorCoefficientState 2)).re) -
        (iteratedDeriv 3
          (fun z : ℂ =>
            canonicalC3AllCutoffMixedSourceTfvdFinalReadout (M + 1) z 0
                q hqpos.le hq1 S
                (canonicalC3AllCutoffMixedSourceTfvdAnalysis q S
                  (canonicalC3AllCutoffMixedSourcePrefixState (M + 1)
                    (operatorHeightParameter z) (operatorHeightParameter 0))) /
              (mixedHermitianWeight canonicalC3ChartFactorHeight z 0 *
                ((2 : ℂ) * completedNativeOperatorCharacteristic z *
                  (starRingEnd ℂ) (completedNativeOperatorCharacteristic 0)))) 0 /
          (3 : ℕ).factorial).re := by
  rw [canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual_eq
      M q hqpos hq1 S,
    canonicalCompletedNativeTfvdCorrectedThirdVariation_eq_fullSixChannelFinalReadoutJet
      M q hqpos hq1 S]

/-- The same unresolved scalar after passing to the actual available
positive dressed carrier.  At first odd order no residual-ray correction is
left: the remaining difference is solely between a positive diagonal and the
corrected signed six-channel third variation. -/
theorem canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual_eq_dressed_sub_correctedThirdVariation
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual
        M q hqpos.le hq1 S =
      canonicalCompletedNativeTfvdDressedFirstOddDiagonal -
        canonicalCompletedNativeTfvdCorrectedThirdVariation M q hqpos.le hq1 S := by
  unfold canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual
  rw [canonicalCompletedNativeTfvdDressedFirstOddDiagonal_eq_raw]

/-- The remaining positive-to-signed sewing equality can be stated without
mentioning the raw carrier: it is exactly vanishing of the same explicit
residual on the canonical dressed first-odd diagonal. -/
theorem canonicalCompletedNativeTfvdDressedFirstOdd_eq_correctedThirdVariation_iff :
    ∀ (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
      (S : Finset NativeGpreBoundaryContext),
      canonicalCompletedNativeTfvdDressedFirstOddDiagonal =
        canonicalCompletedNativeTfvdCorrectedThirdVariation M q hqpos.le hq1 S ↔
      canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual
        M q hqpos.le hq1 S = 0 := by
  intro M q hqpos hq1 S
  rw [canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual_eq_dressed_sub_correctedThirdVariation
    M q hqpos hq1 S]
  exact sub_eq_zero.symm

/-- Fully geometric spelling of the remaining second-layer scalar: the
positive dressed first-odd diagonal minus the signed third coefficient of the
full chiral Wronskian balance.  No moment positivity occurs in this identity.
-/
theorem canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual_eq_dressed_sub_signedChiralThirdVariation
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual
        M q hqpos.le hq1 S =
      canonicalCompletedNativeTfvdDressedFirstOddDiagonal -
        (canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M 3).re := by
  rw [canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual_eq_dressed_sub_correctedThirdVariation
      M q hqpos hq1 S,
    canonicalCompletedNativeTfvdCorrectedThirdVariation_eq_signedChiralThirdVariation
      M q hqpos hq1 S]

/-- The same residual expressed against the completed third response
coefficient `C`. -/
theorem canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual_eq_raw_sub_completedResponse
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual
        M q hqpos.le hq1 S =
      canonicalCompletedNativeTfvdFirstOddRawDiagonal -
        canonicalCompletedNativeCompletedResponseThirdCoefficient := by
  unfold canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual
  rw [canonicalCompletedNativeTfvdCorrectedThirdVariation_eq_completedResponseCoefficient
    M q hqpos hq1 S]

/-- Vanishing of the explicit residual is equivalent to the existing named
raw-first-odd identification.  This pins the only unproved second-layer
sewing statement to one scalar equality rather than treating it as a hidden
positivity assumption. -/
theorem canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual_eq_zero_iff :
    ∀ (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
      (S : Finset NativeGpreBoundaryContext),
      canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual
          M q hqpos.le hq1 S = 0 ↔
        CanonicalCompletedNativeTfvdFirstOddDiagonalMomentIdentification := by
  intro M q hqpos hq1 S
  rw [canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual_eq_raw_sub_completedResponse
    M q hqpos hq1 S,
    canonicalCompletedNativeCompletedResponseThirdCoefficient_eq_moment_one]
  change canonicalCompletedNativeTfvdFirstOddRawDiagonal -
      canonicalCompletedNativeLogDerivativeMoment 1 = 0 ↔ _
  unfold CanonicalCompletedNativeTfvdFirstOddDiagonalMomentIdentification
    canonicalCompletedNativeTfvdFirstOddRawDiagonal
  exact sub_eq_zero

/-- If, and only if, the explicit raw-to-corrected residual vanishes, the
already-proved positive raw TFVD energy transfers to `h₁`.  This is a
consequence of the sewing equality, not a source for it. -/
theorem canonicalCompletedNativeSecondLayerMoment_pos_of_sewingResidual_eq_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (hsewing : canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual
      M q hqpos.le hq1 S = 0) :
    0 < canonicalCompletedNativeSecondLayerMoment := by
  unfold canonicalCompletedNativeSecondLayerMoment
  apply canonicalCompletedNativeLogDerivativeMoment_one_pos_of_tfvdFirstOddDiagonal
  exact (canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual_eq_zero_iff
    M q hqpos hq1 S).mp hsewing

/-- With an independently geometric positivity certificate for the already
closed first layer, a vanishing second-layer sewing residual makes the first
genuinely two-point determinant slope strictly positive. -/
theorem canonicalCompletedNativeTwoPointDiagnosticSlope_pos_of_sewingResidual_eq_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (hmomentZero : 0 < canonicalCompletedNativeLogDerivativeMoment 0)
    (hsewing : canonicalCompletedNativeTfvdFirstOddSecondLayerSewingResidual
      M q hqpos.le hq1 S = 0) :
    0 < 4 * canonicalCompletedNativeLogDerivativeMoment 0 *
      canonicalCompletedNativeSecondLayerMoment := by
  have hmomentOne :=
    canonicalCompletedNativeSecondLayerMoment_pos_of_sewingResidual_eq_zero
      M q hqpos hq1 S hsewing
  positivity

/-- The scalar diagnostic for the genuinely two-point radial sector.  It is
recorded here only to locate the order at which `h₁` first appears; no
Herglotz positivity is used in this audit. -/
theorem canonicalCompletedNativeReducedRadialTwoPointDeterminant_deriv_diagnostic :
    HasDerivAt completedNativeReducedRadialHerglotzTwoDeterminant
      (4 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) *
        canonicalCompletedNativeSecondLayerMoment) 0 := by
  simpa [canonicalCompletedNativeSecondLayerMoment] using
    hasDerivAt_completedNativeReducedRadialHerglotzTwoDeterminant_zero

/-- The analytic fourth-order formula for the same `D`; it is a readback,
not a source of positivity. -/
theorem canonicalCompletedNativeSecondLayerMoment_eq_fourthOrderDiscriminant :
    canonicalCompletedNativeSecondLayerMoment =
      (completedNativeRealEvenCharacteristicCoefficient 1 ^ 2 -
        2 * completedNativeRealEvenCharacteristicCoefficient 0 *
          completedNativeRealEvenCharacteristicCoefficient 2) /
        completedNativeRealEvenCharacteristicCoefficient 0 ^ 2 := by
  exact canonicalCompletedNativeLogDerivativeMoment_one_eq_fourthOrderDiscriminant

end

end CarrySelfAdjointOperator
