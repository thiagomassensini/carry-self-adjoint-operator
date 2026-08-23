import CarrySelfAdjointOperator.CompletedEnrichedTfvdBoundaryCompanion
import CarrySelfAdjointOperator.CanonicalC3StripScalarization
import CarrySelfAdjointOperator.CanonicalC3GammaEnergyNormalization
import CarrySelfAdjointOperator.CompletedTfvdCanonicalSourceIntertwining
import CarrySelfAdjointOperator.CanonicalEnrichedBoundaryResidualIdentity
import NativeCarryC3Crosswalk.CanonicalNaimarkStateReadout
import NativeCarryC3Crosswalk.EnrichedTfvdPairTailClosure
import NativeCarrySpectralWeyl.Boundary.GreenRelation

/-!
# Canonical C3 global-camera boundary bridge

The complete C3 port has a bounded faithful realization in the all-bases
Naimark space.  This file specializes that realization to the canonical
completed state and proves that the canonical Naimark adjoint recovers exactly
the six-camera source already used by the gamma field.

The completed enriched TFVD value and companion are independently identified
with the completed characteristic and its native boundary companion.  Hence
the remaining Wronskian seam is exactly the compatibility of this enriched
boundary pair with the all-bases Cauchy trace.  No scalarization or zero
confinement statement is assumed or manufactured here.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite
open Filter

noncomputable section

/-- The scalar Wronskian is literally the Green form of the algebraic
boundary pair `(Psi, F)`. -/
theorem completedGreenWronskian_eq_scalarGreenForm
    (F Psi : ℂ → ℂ) (z w : ℂ) :
    completedGreenWronskian F Psi z w =
      NativeCarrySpectralWeyl.Boundary.greenForm (𝕜 := ℂ)
        (Psi w, F w) (Psi z, F z) := by
  simp [completedGreenWronskian,
    NativeCarrySpectralWeyl.Boundary.greenForm]

/-- The canonical completed C3 state promoted to the global all-bases
Naimark realization. -/
def canonicalCompletedC3NaimarkState (z : ℂ) :
    RealifiedNaimarkComplexification :=
  NativeCarryC3Crosswalk.c3SixCameraNaimarkRealization
    (canonicalCompletedOperatorC3State z)

/-- The global Naimark state is exactly the canonical Naimark port applied to
the private/public six-camera source. -/
theorem canonicalCompletedC3NaimarkState_eq_realifiedNaimarkPort
    (z : ℂ) :
    canonicalCompletedC3NaimarkState z =
      realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z) := by
  unfold canonicalCompletedC3NaimarkState
    NativeCarryC3Crosswalk.c3SixCameraNaimarkRealization
    canonicalCompletedC3SixCameraSource
  rw [canonicalC3SixCameraSourceMap_eq_publicPacking]
  rfl

/-- The canonical all-bases adjoint readout recovers the completed C3 source
without a selected inverse or a scalar synthesis. -/
theorem canonicalCompletedC3GlobalCameraReadout_eq_source
    (z : ℂ) :
    NativeCarryC3Crosswalk.canonicalCameraStateReadout
        NativeCarryC3Crosswalk.c3SixCameraNaimarkRealization
        (canonicalCompletedOperatorC3State z) =
      canonicalCompletedC3SixCameraSource z := by
  rw [NativeCarryC3Crosswalk.canonicalCameraStateReadout_c3SixCameraNaimarkRealization]
  exact (canonicalC3SixCameraSourceMap_eq_publicPacking
    (canonicalCompletedOperatorC3State z)).symm

/-- The same reconstruction law stated directly at the promoted global
Naimark state. -/
theorem realifiedNaimarkAdjoint_canonicalCompletedC3NaimarkState
    (z : ℂ) :
    realifiedNaimarkAdjoint (canonicalCompletedC3NaimarkState z) =
      canonicalCompletedC3SixCameraSource z := by
  simpa only [canonicalCompletedC3NaimarkState,
    NativeCarryC3Crosswalk.canonicalCameraStateReadout_apply] using
    canonicalCompletedC3GlobalCameraReadout_eq_source z

/-- The canonical source seen from the all-bases Naimark ambient space. -/
def canonicalCompletedC3GlobalCameraSource
    (z : ℂ) : RealifiedCameraComplexification :=
  realifiedNaimarkAdjoint (canonicalCompletedC3NaimarkState z)

/-- Global adjoint compression and the canonical completed C3 source agree as
camera-valued functions. -/
theorem canonicalCompletedC3GlobalCameraSource_eq_source :
    canonicalCompletedC3GlobalCameraSource =
      canonicalCompletedC3SixCameraSource := by
  funext z
  exact realifiedNaimarkAdjoint_canonicalCompletedC3NaimarkState z

/-- The ambient logarithmic generator underlying the all-camera Cauchy trace
is self-adjoint. -/
theorem canonicalCompletedC3GlobalLogarithmicGenerator_isSelfAdjoint :
    IsSelfAdjoint
      NativeCarrySpectralWeyl.Infinite.logarithmicMultiplication :=
  NativeCarrySpectralWeyl.Infinite.logarithmicMultiplication_isSelfAdjoint

/-- Its graph is the closed maximal Green boundary relation. -/
theorem canonicalCompletedC3GlobalLogarithmicGreenRelation_isClosed :
    IsClosed
      (NativeCarrySpectralWeyl.Boundary.logarithmicGreenRelation :
        Set (NativeCarrySpectralWeyl.Infinite.NaimarkSpace ×
          NativeCarrySpectralWeyl.Infinite.NaimarkSpace)) :=
  NativeCarrySpectralWeyl.Boundary.logarithmicGreenRelation_isClosed

theorem canonicalCompletedC3GlobalLogarithmicGreenRelation_isMaximal :
    NativeCarrySpectralWeyl.Boundary.IsMaximalGreenIsotropic
      NativeCarrySpectralWeyl.Boundary.logarithmicGreenRelation :=
  NativeCarrySpectralWeyl.Boundary.logarithmicGreenRelation_isMaximalGreenIsotropic

/-- Completion into the global Naimark space does not collapse the canonical
C3 state anywhere above the open Genuine strip. -/
theorem canonicalCompletedC3NaimarkState_ne_zero
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3NaimarkState z ≠ 0 := by
  intro hzero
  apply canonicalEnrichedC3SourcePort_ne_zero hs
  apply NativeCarryC3Crosswalk.c3SixCameraNaimarkRealization_injective
  simpa [canonicalCompletedC3NaimarkState,
    canonicalCompletedOperatorC3State] using hzero

/-- Real symplectic Green reading of the global source and its Cauchy boundary
value. -/
def canonicalCompletedC3GlobalCauchyBoundarySkew
    (z : ℂ) (hz : z.im ≠ 0) : ℝ :=
  NativeCarryC3Crosswalk.realifiedGreenSkew
    (canonicalCompletedC3GlobalCameraSource z)
    (allBasesCauchyBlock z hz
      (canonicalCompletedC3GlobalCameraSource z))

/-- The global symplectic reading is exactly the Cauchy skew used by the gamma
field. -/
theorem canonicalCompletedC3GlobalCauchyBoundarySkew_eq_gammaCauchySkew
    (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3GlobalCauchyBoundarySkew z hz =
      completedGammaCauchySkew
        canonicalCompletedC3GlobalCameraSource z hz := by
  rfl

/-- Oriented complex boundary measure read by the global Cauchy trace. -/
def canonicalCompletedC3GlobalBoundaryGreenTrace
    (z : ℂ) (hz : z.im ≠ 0) : ℂ :=
  (-(2 : ℂ) * Complex.I) *
    (canonicalCompletedC3GlobalCauchyBoundarySkew z hz : ℂ)

/-- The global boundary measure is the spectral skew multiplied by the
positive gamma energy of the completed C3 defect state. -/
theorem canonicalCompletedC3GlobalBoundaryGreenTrace_eq_energy
    (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3GlobalBoundaryGreenTrace z hz =
      (z - (starRingEnd ℂ) z) *
        (canonicalCompletedC3GammaEnergy z : ℂ) := by
  unfold canonicalCompletedC3GlobalBoundaryGreenTrace
  rw [canonicalCompletedC3GlobalCauchyBoundarySkew_eq_gammaCauchySkew]
  rw [canonicalCompletedC3GlobalCameraSource_eq_source]
  exact
    neg_two_i_mul_completedGammaCauchySkew_eq_centeredFactor_mul_energy
      canonicalCompletedC3SixCameraSource z hz

/-- On the open strip and away from the real carry-time axis, the Green
boundary measure cannot vanish. -/
theorem canonicalCompletedC3GlobalBoundaryGreenTrace_ne_zero
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hz : z.im ≠ 0) :
    canonicalCompletedC3GlobalBoundaryGreenTrace z hz ≠ 0 := by
  rw [canonicalCompletedC3GlobalBoundaryGreenTrace_eq_energy z hz]
  apply mul_ne_zero
  · apply sub_ne_zero.mpr
    intro hconj
    apply hz
    exact Complex.conj_eq_iff_im.mp hconj.symm
  · exact_mod_cast ne_of_gt (canonicalCompletedC3GammaEnergy_pos hs hz)

/-! ## Canonically normalized finite no-leak limit -/

/-- Radial-Green channel normalization.  Its information is real before the
final quarter-turn, so `Re` is intentionally applied before multiplication by
`-2 i`.  This map must not be applied to a Wronskian-skew channel. -/
def canonicalCompletedC3BoundaryTraceNormalization (a : ℂ) : ℂ :=
  (-(2 : ℂ) * Complex.I) * (a.re : ℂ)

/-- Orientation of one complex boundary channel.  The channel is rotated
first, projected to its real readout only afterwards, and finally rebuilt in
the oriented complex boundary line. -/
structure CanonicalCompletedC3BoundaryChannelOrientation where
  preRotation : ℂ
  postRotation : ℂ

/-- Channel-local readout with the order `rotation -> Re -> reconstruction`
made explicit. -/
def canonicalCompletedC3RotatedRealChannelReadout
    (orientation : CanonicalCompletedC3BoundaryChannelOrientation)
    (a : ℂ) : ℂ :=
  orientation.postRotation *
    (((orientation.preRotation * a).re : ℝ) : ℂ)

/-- The radial Green channel is already real.  Its final reconstruction is
the existing `-2 i` boundary normalization. -/
def canonicalCompletedC3RadialGreenChannelOrientation :
    CanonicalCompletedC3BoundaryChannelOrientation :=
  ⟨1, -(2 : ℂ) * Complex.I⟩

/-- A Wronskian diagonal is imaginary.  Multiplication by `-i` identifies it
with the real readout line before `Re`; multiplication by `i` restores its
original skew orientation afterwards. -/
def canonicalCompletedC3WronskianSkewChannelOrientation :
    CanonicalCompletedC3BoundaryChannelOrientation :=
  ⟨-Complex.I, Complex.I⟩

/-- Four boundary channels retained until their channel-local final
readouts.  No complex sum is formed in this carrier. -/
structure CanonicalCompletedC3SeparatedBoundaryChannels where
  radialGreen : ℂ
  wronskianSkew : ℂ
  offDiagonal : ℂ
  seamDefect : ℂ

/-- Per-channel orientations for the final readout.  In particular, the
off-diagonal and defect orientations cannot be silently inherited from the
radial channel. -/
structure CanonicalCompletedC3SeparatedBoundaryOrientations where
  radialGreen : CanonicalCompletedC3BoundaryChannelOrientation
  wronskianSkew : CanonicalCompletedC3BoundaryChannelOrientation
  offDiagonal : CanonicalCompletedC3BoundaryChannelOrientation
  seamDefect : CanonicalCompletedC3BoundaryChannelOrientation

/-- Fix the two established channel orientations while leaving the
off-diagonal and seam orientations explicit inputs. -/
def canonicalCompletedC3SeparatedBoundaryOrientationsWith
    (offDiagonal seamDefect :
      CanonicalCompletedC3BoundaryChannelOrientation) :
    CanonicalCompletedC3SeparatedBoundaryOrientations :=
  {
    radialGreen := canonicalCompletedC3RadialGreenChannelOrientation
    wronskianSkew := canonicalCompletedC3WronskianSkewChannelOrientation
    offDiagonal := offDiagonal
    seamDefect := seamDefect
  }

/-- Final readout formed only after every retained channel has undergone its
own rotation and real projection. -/
def canonicalCompletedC3SeparatedBoundaryFinalReadout
    (orientations : CanonicalCompletedC3SeparatedBoundaryOrientations)
    (channels : CanonicalCompletedC3SeparatedBoundaryChannels) : ℂ :=
  canonicalCompletedC3RotatedRealChannelReadout
      orientations.radialGreen channels.radialGreen +
    canonicalCompletedC3RotatedRealChannelReadout
      orientations.wronskianSkew channels.wronskianSkew +
    canonicalCompletedC3RotatedRealChannelReadout
      orientations.offDiagonal channels.offDiagonal +
    canonicalCompletedC3RotatedRealChannelReadout
      orientations.seamDefect channels.seamDefect

theorem canonicalCompletedC3RadialGreenChannelReadout_eq_normalization
    (a : ℂ) :
    canonicalCompletedC3RotatedRealChannelReadout
        canonicalCompletedC3RadialGreenChannelOrientation a =
      canonicalCompletedC3BoundaryTraceNormalization a := by
  simp [canonicalCompletedC3RotatedRealChannelReadout,
    canonicalCompletedC3RadialGreenChannelOrientation,
    canonicalCompletedC3BoundaryTraceNormalization]

/-- The skew-channel order preserves every purely imaginary boundary datum. -/
theorem canonicalCompletedC3WronskianSkewChannelReadout_eq_self_of_re_eq_zero
    {a : ℂ} (ha : a.re = 0) :
    canonicalCompletedC3RotatedRealChannelReadout
        canonicalCompletedC3WronskianSkewChannelOrientation a = a := by
  apply Complex.ext
  · simp [canonicalCompletedC3RotatedRealChannelReadout,
      canonicalCompletedC3WronskianSkewChannelOrientation,
      Complex.mul_re, ha]
  · simp [canonicalCompletedC3RotatedRealChannelReadout,
      canonicalCompletedC3WronskianSkewChannelOrientation,
      Complex.mul_re]

/-- Every diagonal scalar Wronskian survives the rotate-first skew readout. -/
theorem canonicalCompletedC3WronskianSkewChannelReadout_completedWronskian
    (F Psi : ℂ → ℂ) (z : ℂ) :
    canonicalCompletedC3RotatedRealChannelReadout
        canonicalCompletedC3WronskianSkewChannelOrientation
        (completedGreenWronskian F Psi z z) =
      completedGreenWronskian F Psi z z := by
  apply
    canonicalCompletedC3WronskianSkewChannelReadout_eq_self_of_re_eq_zero
  simp [completedGreenWronskian, Complex.mul_re]
  ring

/-- Applying the radial readout to a diagonal Wronskian is the premature
normalization error: it annihilates the entire skew channel. -/
theorem canonicalCompletedC3RadialGreenChannelReadout_completedWronskian_eq_zero
    (F Psi : ℂ → ℂ) (z : ℂ) :
    canonicalCompletedC3BoundaryTraceNormalization
        (completedGreenWronskian F Psi z z) = 0 := by
  unfold canonicalCompletedC3BoundaryTraceNormalization
  have hre : (completedGreenWronskian F Psi z z).re = 0 := by
    simp [completedGreenWronskian, Complex.mul_re]
    ring
  rw [hre]
  simp

/-- Concrete witness that summing radial and skew channels before applying
the radial projection is not equivalent to their channelwise final readout. -/
theorem canonicalCompletedC3EarlyRadialNormalization_ne_separatedReadout :
    canonicalCompletedC3BoundaryTraceNormalization (1 + Complex.I) ≠
      canonicalCompletedC3BoundaryTraceNormalization 1 +
        canonicalCompletedC3RotatedRealChannelReadout
          canonicalCompletedC3WronskianSkewChannelOrientation Complex.I := by
  intro h
  have him := congrArg Complex.im h
  norm_num [canonicalCompletedC3BoundaryTraceNormalization,
    canonicalCompletedC3RotatedRealChannelReadout,
    canonicalCompletedC3WronskianSkewChannelOrientation,
    Complex.mul_re, Complex.mul_im] at him

/-- Canonical finite coupled C3 ledger before passage to the completed
boundary. -/
def canonicalCompletedC3FiniteCoupledBoundaryReadout
    (M : ℕ) (s : ℂ) : ℂ :=
  finiteCanonicalTfvdCoupledGenuineGreenFlux 3 M s

/-- Polarized scalar boundary read directly from the finite ordinary/log-jet
ledger before adding its nonlocal tail and completion factors. -/
def canonicalCompletedC3FinitePolarizedScalarBoundaryReadout
    (M : ℕ) (s : ℂ) : ℂ :=
  scalarBoundaryWedge
    (canonicalBoundaryResidualData M tfvdHaarScale
      (fun _ : ℕ => (1 : ℂ)) s).valueReadout
    (canonicalBoundaryResidualData M tfvdHaarScale
      (fun _ : ℕ => (1 : ℂ)) s).logJetReadout

/-- Explicit finite sewing account between the coupled C3 ledger and the
polarized scalar readout.  Every term is an independently constructed channel:
the aligned angular boundary, Green provenance, cross-edge provenance, and
the four readout residuals. -/
def canonicalCompletedC3FinitePolarizedSeamDefect
    (M : ℕ) (s : ℂ) : ℂ :=
  finiteCanonicalAngularBracketCoupledBoundary M s -
    (finiteCanonicalTfvdSameSGreenProvenanceDefect 3 M s +
      canonicalBoundaryCrossProvenance M tfvdHaarScale
        (fun _ : ℕ => (1 : ℂ)) s +
      canonicalBoundaryReadoutResidualCorrection M tfvdHaarScale
        (fun _ : ℕ => (1 : ℂ)) s)

/-- The actual four finite channels, assembled only as a product carrier.
The off-diagonal term is not absorbed into the remaining seam account. -/
def canonicalCompletedC3FiniteSeparatedBoundaryChannels
    (M : ℕ) (s : ℂ) : CanonicalCompletedC3SeparatedBoundaryChannels :=
  {
    radialGreen :=
      NativeCarrySpectralWeyl.Boundary.greenForm (𝕜 := ℂ)
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
          (3 * M) s)
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
          (3 * M) (reflectedParameter s))
    wronskianSkew :=
      canonicalCompletedC3FinitePolarizedScalarBoundaryReadout M s
    offDiagonal :=
      canonicalBoundaryCrossProvenance M tfvdHaarScale
        (fun _ : ℕ => (1 : ℂ)) s
    seamDefect :=
      finiteCanonicalAngularBracketCoupledBoundary M s -
        (finiteCanonicalTfvdSameSGreenProvenanceDefect 3 M s +
          canonicalBoundaryReadoutResidualCorrection M tfvdHaarScale
            (fun _ : ℕ => (1 : ℂ)) s)
  }

/-! ## Tail-completed separated scalar readout -/

/-- Value coordinate of the finite enriched TFVD transport after adjoining
the unresolved tail of the same C3 bracket series.  This is constructed at
cutoff `M`; it is not defined from the completed characteristic. -/
def canonicalCompletedC3FiniteEnrichedTfvdValueTailReadout
    (M : ℕ) (s : ℂ) : ℂ :=
  NativeCarryC3Crosswalk.finiteC3CanonicalEnrichedTfvdPairTailReadout
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) s

/-- Log-jet coordinate completed with the differentiated unresolved C3 tail
at the same cutoff as the value coordinate. -/
def canonicalCompletedC3FiniteEnrichedTfvdLogJetTailReadout
    (M : ℕ) (s : ℂ) : ℂ :=
  finiteCanonicalLogBracketChart M s + canonicalC3LogJetCutoffTail M s

/-- Every cutoff-completed value coordinate is the canonical completed value
coordinate.  Both sides independently reconstruct the same infinite bracket
chart by head-plus-tail decomposition. -/
theorem canonicalCompletedC3FiniteEnrichedTfvdValueTailReadout_eq_completed
    (M : ℕ) {s : ℂ} (hs : s ∈ bracketHalfPlane) :
    canonicalCompletedC3FiniteEnrichedTfvdValueTailReadout M s =
      canonicalCompletedC3EnrichedTfvdValueTailReadout s := by
  have hsRe : -1 < s.re := by simpa [bracketHalfPlane] using hs
  unfold canonicalCompletedC3FiniteEnrichedTfvdValueTailReadout
    canonicalCompletedC3EnrichedTfvdValueTailReadout
  rw [
    NativeCarryC3Crosswalk.finiteC3CanonicalEnrichedTfvdPairTailReadout_eq_chart
      M tfvdHaarScale_ne_zero (fun _ : ℕ => (1 : ℂ))
      (by intro m; norm_num) hsRe,
    NativeCarryC3Crosswalk.finiteC3CanonicalEnrichedTfvdPairTailReadout_eq_chart
      1 tfvdHaarScale_ne_zero (fun _ : ℕ => (1 : ℂ))
      (by intro m; norm_num) hsRe]

/-- The head log-jet plus its differentiated tail is independent of the
cutoff: it is exactly minus the derivative of the complete bracket chart. -/
theorem canonicalCompletedC3FiniteEnrichedTfvdLogJetTailReadout_eq_neg_deriv
    (M : ℕ) {s : ℂ} (hs : s ∈ bracketHalfPlane) :
    canonicalCompletedC3FiniteEnrichedTfvdLogJetTailReadout M s =
      -deriv (bracketedDirichletChart 3) s := by
  have hhead :=
    hasDerivAt_finiteBracketedDirichletChart_three_eq_neg_logJet M s
  have htail :=
    hasDerivAt_realCpBracketCutoffTail_eq_neg_logJetTail M hs
  have hsum :
      HasDerivAt
        (fun u : ℂ =>
          finiteBracketedDirichletChart 3 M u +
            realCpBracketCutoffTail 3 M u)
        ((-finiteCanonicalLogBracketChart M s) +
          (-canonicalC3LogJetCutoffTail M s)) s :=
    hhead.add htail
  have hfunctions :
      (fun u : ℂ =>
        finiteBracketedDirichletChart 3 M u +
          realCpBracketCutoffTail 3 M u) =ᶠ[nhds s]
        bracketedDirichletChart 3 := by
    filter_upwards [isOpen_bracketHalfPlane.mem_nhds hs] with u hu
    exact (bracketedDirichletChart_eq_finite_add_cutoffTail
      3 M (by norm_num) (by simpa [bracketHalfPlane] using hu)).symm
  have hsumDeriv :
      deriv
          (fun u : ℂ =>
            finiteBracketedDirichletChart 3 M u +
              realCpBracketCutoffTail 3 M u) s =
        (-finiteCanonicalLogBracketChart M s) +
          (-canonicalC3LogJetCutoffTail M s) := by
    exact hsum.deriv
  have hfunctionsDeriv :
      deriv
          (fun u : ℂ =>
            finiteBracketedDirichletChart 3 M u +
              realCpBracketCutoffTail 3 M u) s =
        deriv (bracketedDirichletChart 3) s := by
    simpa only [Pi.add_apply] using hfunctions.deriv_eq
  unfold canonicalCompletedC3FiniteEnrichedTfvdLogJetTailReadout
  calc
    finiteCanonicalLogBracketChart M s + canonicalC3LogJetCutoffTail M s =
        -((-finiteCanonicalLogBracketChart M s) +
          (-canonicalC3LogJetCutoffTail M s)) := by ring
    _ = -deriv
          (fun u : ℂ =>
            finiteBracketedDirichletChart 3 M u +
              realCpBracketCutoffTail 3 M u) s := by
      rw [hsumDeriv]
    _ = -deriv (bracketedDirichletChart 3) s := by
      rw [hfunctionsDeriv]

/-- The independently tail-completed log-jet at every cutoff is the same
canonical completed enriched log-jet. -/
theorem canonicalCompletedC3FiniteEnrichedTfvdLogJetTailReadout_eq_completed
    (M : ℕ) {s : ℂ} (hs : s ∈ bracketHalfPlane) :
    canonicalCompletedC3FiniteEnrichedTfvdLogJetTailReadout M s =
      canonicalCompletedC3EnrichedTfvdLogJetTailReadout s := by
  calc
    canonicalCompletedC3FiniteEnrichedTfvdLogJetTailReadout M s =
        -deriv (bracketedDirichletChart 3) s :=
      canonicalCompletedC3FiniteEnrichedTfvdLogJetTailReadout_eq_neg_deriv
        M hs
    _ = canonicalCompletedC3FiniteEnrichedTfvdLogJetTailReadout 1 s :=
      (canonicalCompletedC3FiniteEnrichedTfvdLogJetTailReadout_eq_neg_deriv
        1 hs).symm
    _ = canonicalCompletedC3EnrichedTfvdLogJetTailReadout s := by
      unfold canonicalCompletedC3FiniteEnrichedTfvdLogJetTailReadout
        canonicalCompletedC3EnrichedTfvdLogJetTailReadout
      rw [(canonicalCompletedC3EnrichedTfvdTransport_components s).2.1]

/-- Cutoff-indexed normalized value coordinate, before xi completion. -/
def canonicalCompletedC3FiniteEnrichedTfvdNormalizedValueTailReadout
    (M : ℕ) (z : ℂ) : ℂ :=
  canonicalCompletedC3FiniteEnrichedTfvdValueTailReadout M
      (operatorHeightParameter z) /
    cpChartFactor 3 (operatorHeightParameter z)

/-- Cutoff-indexed normalized companion of the value coordinate.  The value
and log-jet tails are kept separate until this quotient-rule readout. -/
def canonicalCompletedC3FiniteEnrichedTfvdNormalizedLogJetTailReadout
    (M : ℕ) (z : ℂ) : ℂ :=
  let s := operatorHeightParameter z
  Complex.I *
    ((canonicalCompletedC3FiniteEnrichedTfvdLogJetTailReadout M s *
          cpChartFactor 3 s +
        canonicalCompletedC3FiniteEnrichedTfvdValueTailReadout M s *
          deriv (cpChartFactor 3) s) /
      cpChartFactor 3 s ^ 2)

theorem canonicalCompletedC3FiniteEnrichedTfvdNormalizedValueTailReadout_eq_completed
    (M : ℕ) {z : ℂ}
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3FiniteEnrichedTfvdNormalizedValueTailReadout M z =
      canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout z := by
  have hsHalf : operatorHeightParameter z ∈ bracketHalfPlane := by
    change -1 < (operatorHeightParameter z).re
    linarith [hs.1]
  unfold canonicalCompletedC3FiniteEnrichedTfvdNormalizedValueTailReadout
    canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout
  rw [canonicalCompletedC3FiniteEnrichedTfvdValueTailReadout_eq_completed
    M hsHalf]

theorem canonicalCompletedC3FiniteEnrichedTfvdNormalizedLogJetTailReadout_eq_completed
    (M : ℕ) {z : ℂ}
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3FiniteEnrichedTfvdNormalizedLogJetTailReadout M z =
      canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout z := by
  have hsHalf : operatorHeightParameter z ∈ bracketHalfPlane := by
    change -1 < (operatorHeightParameter z).re
    linarith [hs.1]
  unfold canonicalCompletedC3FiniteEnrichedTfvdNormalizedLogJetTailReadout
    canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout
  dsimp only
  rw [canonicalCompletedC3FiniteEnrichedTfvdLogJetTailReadout_eq_completed
      M hsHalf,
    canonicalCompletedC3FiniteEnrichedTfvdValueTailReadout_eq_completed
      M hsHalf]

/-- Xi-completed value coordinate built from cutoff `M` and its explicit C3
tail. -/
def canonicalCompletedC3FiniteEnrichedTfvdCompletedValueTailReadout
    (M : ℕ) (z : ℂ) : ℂ :=
  nativeXiCompletionFactor z *
    canonicalCompletedC3FiniteEnrichedTfvdNormalizedValueTailReadout M z

/-- Xi-completed companion built from the separately retained normalized
value and log-jet channels at cutoff `M`. -/
def canonicalCompletedC3FiniteEnrichedTfvdBoundaryCompanion
    (M : ℕ) (z : ℂ) : ℂ :=
  productBoundaryCompanion
    nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion
    (canonicalCompletedC3FiniteEnrichedTfvdNormalizedValueTailReadout M)
    (canonicalCompletedC3FiniteEnrichedTfvdNormalizedLogJetTailReadout M) z

theorem canonicalCompletedC3FiniteEnrichedTfvdCompletedValueTailReadout_eq_completed
    (M : ℕ) {z : ℂ}
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3FiniteEnrichedTfvdCompletedValueTailReadout M z =
      canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout z := by
  unfold canonicalCompletedC3FiniteEnrichedTfvdCompletedValueTailReadout
    canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
  rw [canonicalCompletedC3FiniteEnrichedTfvdNormalizedValueTailReadout_eq_completed
    M hs]

theorem canonicalCompletedC3FiniteEnrichedTfvdBoundaryCompanion_eq_completed
    (M : ℕ) {z : ℂ}
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3FiniteEnrichedTfvdBoundaryCompanion M z =
      canonicalCompletedC3EnrichedTfvdBoundaryCompanion z := by
  unfold canonicalCompletedC3FiniteEnrichedTfvdBoundaryCompanion
    canonicalCompletedC3EnrichedTfvdBoundaryCompanion
    productBoundaryCompanion
  rw [
    canonicalCompletedC3FiniteEnrichedTfvdNormalizedValueTailReadout_eq_completed
      M hs,
    canonicalCompletedC3FiniteEnrichedTfvdNormalizedLogJetTailReadout_eq_completed
      M hs]

/-- The finite four-channel ledger with only its scalar skew coordinate
replaced by the independently tail- and xi-completed enriched TFVD pair.  The
radial, off-diagonal, and seam coordinates remain present and unmerged. -/
def canonicalCompletedC3FiniteEnrichedSeparatedBoundaryChannels
    (M : ℕ) (z : ℂ) : CanonicalCompletedC3SeparatedBoundaryChannels :=
  { canonicalCompletedC3FiniteSeparatedBoundaryChannels M
      (operatorHeightParameter z) with
    wronskianSkew :=
      scalarBoundaryWedge
        (canonicalCompletedC3FiniteEnrichedTfvdCompletedValueTailReadout M z)
        (canonicalCompletedC3FiniteEnrichedTfvdBoundaryCompanion M z) }

/-- The final scalar readout is the skew projection of the separated ledger.
The other three provenance channels remain available for independent Green
and no-leak audits and are not silently added to the scalar Wronskian. -/
def canonicalCompletedC3FinalScalarReadout
    (channels : CanonicalCompletedC3SeparatedBoundaryChannels) : ℂ :=
  canonicalCompletedC3RotatedRealChannelReadout
    canonicalCompletedC3WronskianSkewChannelOrientation
    channels.wronskianSkew

/-- The tail-completed enriched separated ledger has exactly the completed
Wronskian as its final scalar readout, at every cutoff. -/
theorem finalScalarReadout_eq_completedWronskian
    (M : ℕ) {z : ℂ}
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3FinalScalarReadout
        (canonicalCompletedC3FiniteEnrichedSeparatedBoundaryChannels M z) =
      completedGreenWronskian
        canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
        canonicalCompletedC3EnrichedTfvdBoundaryCompanion z z := by
  unfold canonicalCompletedC3FinalScalarReadout
    canonicalCompletedC3FiniteEnrichedSeparatedBoundaryChannels
  rw [
    canonicalCompletedC3FiniteEnrichedTfvdCompletedValueTailReadout_eq_completed
      M hs,
    canonicalCompletedC3FiniteEnrichedTfvdBoundaryCompanion_eq_completed
      M hs]
  rw [show scalarBoundaryWedge
      (canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout z)
      (canonicalCompletedC3EnrichedTfvdBoundaryCompanion z) =
        completedGreenWronskian
          canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
          canonicalCompletedC3EnrichedTfvdBoundaryCompanion z z by
    simp [scalarBoundaryWedge, completedGreenWronskian]
    ring]
  exact canonicalCompletedC3WronskianSkewChannelReadout_completedWronskian
    _ _ z

/-- Limit form of the exact scalar sewing theorem. -/
theorem finalScalarReadout_tendsto_completedWronskian
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ =>
        canonicalCompletedC3FinalScalarReadout
          (canonicalCompletedC3FiniteEnrichedSeparatedBoundaryChannels M z))
      atTop
      (nhds
        (completedGreenWronskian
          canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
          canonicalCompletedC3EnrichedTfvdBoundaryCompanion z z)) := by
  have hfunctions :
      (fun M : ℕ =>
        canonicalCompletedC3FinalScalarReadout
          (canonicalCompletedC3FiniteEnrichedSeparatedBoundaryChannels M z)) =
        (fun _ : ℕ =>
          completedGreenWronskian
            canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
            canonicalCompletedC3EnrichedTfvdBoundaryCompanion z z) := by
    funext M
    exact finalScalarReadout_eq_completedWronskian M hs
  rw [hfunctions]
  exact tendsto_const_nhds

/-- Explicit mismatch between the cutoff-indexed final scalar readout and the
completed Wronskian. -/
def canonicalCompletedC3FinalScalarReadoutDefect
    (M : ℕ) (z : ℂ) : ℂ :=
  canonicalCompletedC3FinalScalarReadout
      (canonicalCompletedC3FiniteEnrichedSeparatedBoundaryChannels M z) -
    completedGreenWronskian
      canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
      canonicalCompletedC3EnrichedTfvdBoundaryCompanion z z

/-- Head-plus-tail completion leaves no scalar sewing defect at any cutoff. -/
theorem canonicalCompletedC3FinalScalarReadoutDefect_eq_zero
    (M : ℕ) {z : ℂ}
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3FinalScalarReadoutDefect M z = 0 := by
  rw [canonicalCompletedC3FinalScalarReadoutDefect,
    finalScalarReadout_eq_completedWronskian M hs, sub_self]

/-- In particular, the explicit scalar sewing defect tends to zero. -/
theorem canonicalCompletedC3FinalScalarReadoutDefect_tendsto_zero
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ => canonicalCompletedC3FinalScalarReadoutDefect M z)
      atTop (nhds 0) := by
  have hfunctions :
      (fun M : ℕ => canonicalCompletedC3FinalScalarReadoutDefect M z) =
        (fun _ : ℕ => (0 : ℂ)) := by
    funext M
    exact canonicalCompletedC3FinalScalarReadoutDefect_eq_zero M hs
  rw [hfunctions]
  exact tendsto_const_nhds

/-- The previous explicit seam is the difference of the retained seam and
off-diagonal channels, not an early scalar collapse of them. -/
theorem canonicalCompletedC3FinitePolarizedSeamDefect_eq_separatedChannels
    (M : ℕ) (s : ℂ) :
    canonicalCompletedC3FinitePolarizedSeamDefect M s =
      (canonicalCompletedC3FiniteSeparatedBoundaryChannels M s).seamDefect -
        (canonicalCompletedC3FiniteSeparatedBoundaryChannels M s).offDiagonal := by
  unfold canonicalCompletedC3FinitePolarizedSeamDefect
    canonicalCompletedC3FiniteSeparatedBoundaryChannels
  ring

/-- The finite scalar boundary is literally a diagonal Wronskian of the two
ledger readouts. -/
theorem canonicalCompletedC3FinitePolarizedScalarBoundaryReadout_eq_wronskian
    (M : ℕ) (s : ℂ) :
    canonicalCompletedC3FinitePolarizedScalarBoundaryReadout M s =
      completedGreenWronskian
        (fun u : ℂ =>
          (canonicalBoundaryResidualData M tfvdHaarScale
            (fun _ : ℕ => (1 : ℂ)) u).valueReadout)
        (fun u : ℂ =>
          (canonicalBoundaryResidualData M tfvdHaarScale
            (fun _ : ℕ => (1 : ℂ)) u).logJetReadout)
        s s := by
  simp [canonicalCompletedC3FinitePolarizedScalarBoundaryReadout,
    scalarBoundaryWedge, completedGreenWronskian]
  ring

/-- The finite polarized Wronskian channel is preserved by its rotate-first
readout. -/
theorem canonicalCompletedC3WronskianSkewChannelReadout_finitePolarized
    (M : ℕ) (s : ℂ) :
    canonicalCompletedC3RotatedRealChannelReadout
        canonicalCompletedC3WronskianSkewChannelOrientation
        (canonicalCompletedC3FinitePolarizedScalarBoundaryReadout M s) =
      canonicalCompletedC3FinitePolarizedScalarBoundaryReadout M s := by
  rw [canonicalCompletedC3FinitePolarizedScalarBoundaryReadout_eq_wronskian]
  exact
    canonicalCompletedC3WronskianSkewChannelReadout_completedWronskian
      _ _ s

/-- Concrete spelling of the same finite scalar Wronskian in the canonical
bracket value and logarithmic-jet coordinates. -/
theorem canonicalCompletedC3FinitePolarizedScalarBoundaryReadout_eq_chart_logJet
    (M : ℕ) (s : ℂ) :
    canonicalCompletedC3FinitePolarizedScalarBoundaryReadout M s =
      scalarBoundaryWedge
        (finiteBracketedDirichletChart 3 M s)
        (finiteCanonicalLogBracketChart M s) := by
  have htransport :=
    NativeCarryC3Crosswalk.finiteC3EnrichedTfvdPairTransport_canonical
      M tfvdHaarScale_ne_zero (fun _ : ℕ => (1 : ℂ))
      (by intro m; norm_num) s
  dsimp only at htransport
  unfold canonicalCompletedC3FinitePolarizedScalarBoundaryReadout
    canonicalBoundaryResidualData canonicalBoundaryResidualPair
  rw [htransport.1, htransport.2.1]

/-- Exact finite polarized decomposition

`coupled ledger = scalar Wronskian readout + explicit seam defect`.

No defect is defined as the residual of this equality. -/
theorem canonicalCompletedC3FiniteCoupledBoundaryReadout_eq_polarized_add_seam
    (M : ℕ) (s : ℂ) :
    canonicalCompletedC3FiniteCoupledBoundaryReadout M s =
      canonicalCompletedC3FinitePolarizedScalarBoundaryReadout M s +
        canonicalCompletedC3FinitePolarizedSeamDefect M s := by
  have hscalar :=
    canonicalEnrichedScalarBoundary_eq_green_add_explicitDefects
      M tfvdHaarScale_ne_zero (fun _ : ℕ => (1 : ℂ))
      (by intro m; norm_num) s
  have hcoupled :
      canonicalCompletedC3FiniteCoupledBoundaryReadout M s =
        NativeCarrySpectralWeyl.Boundary.greenForm (𝕜 := ℂ)
            (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
              (3 * M) s)
            (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
              (3 * M) (reflectedParameter s)) +
          finiteCanonicalAngularBracketCoupledBoundary M s := by
    unfold canonicalCompletedC3FiniteCoupledBoundaryReadout
      finiteCanonicalTfvdCoupledGenuineGreenFlux
    rw [NativeCarryC3Crosswalk.greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_genuineFlux]
  unfold canonicalCompletedC3FinitePolarizedScalarBoundaryReadout
    canonicalCompletedC3FinitePolarizedSeamDefect
  rw [hcoupled]
  linear_combination -hscalar

/-- Complete finite four-channel ledger.  The radial Green identity, the
polarized Wronskian expansion, and their sewing relation hold simultaneously
without projecting or merging any channel. -/
theorem canonicalCompletedC3FiniteSeparatedBoundaryChannels_ledger
    (M : ℕ) (s : ℂ) :
    (canonicalCompletedC3FiniteCoupledBoundaryReadout M s =
      (canonicalCompletedC3FiniteSeparatedBoundaryChannels M s).radialGreen +
        finiteCanonicalAngularBracketCoupledBoundary M s) ∧
    ((canonicalCompletedC3FiniteSeparatedBoundaryChannels M s).wronskianSkew =
      (canonicalCompletedC3FiniteSeparatedBoundaryChannels M s).radialGreen +
        finiteCanonicalTfvdSameSGreenProvenanceDefect 3 M s +
        (canonicalCompletedC3FiniteSeparatedBoundaryChannels M s).offDiagonal +
        canonicalBoundaryReadoutResidualCorrection M tfvdHaarScale
          (fun _ : ℕ => (1 : ℂ)) s) ∧
    (canonicalCompletedC3FiniteCoupledBoundaryReadout M s =
      (canonicalCompletedC3FiniteSeparatedBoundaryChannels M s).wronskianSkew +
        (canonicalCompletedC3FiniteSeparatedBoundaryChannels M s).seamDefect -
        (canonicalCompletedC3FiniteSeparatedBoundaryChannels M s).offDiagonal) := by
  constructor
  · unfold canonicalCompletedC3FiniteCoupledBoundaryReadout
      finiteCanonicalTfvdCoupledGenuineGreenFlux
      canonicalCompletedC3FiniteSeparatedBoundaryChannels
    rw [NativeCarryC3Crosswalk.greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_genuineFlux]
  constructor
  · have hscalar :=
      canonicalEnrichedScalarBoundary_eq_green_add_explicitDefects
        M tfvdHaarScale_ne_zero (fun _ : ℕ => (1 : ℂ))
        (by intro m; norm_num) s
    simpa [canonicalCompletedC3FiniteSeparatedBoundaryChannels,
      canonicalCompletedC3FinitePolarizedScalarBoundaryReadout,
      add_assoc] using hscalar
  · rw [canonicalCompletedC3FiniteCoupledBoundaryReadout_eq_polarized_add_seam,
      canonicalCompletedC3FinitePolarizedSeamDefect_eq_separatedChannels]
    simp only [canonicalCompletedC3FiniteSeparatedBoundaryChannels]
    ring

/-- Expansion of the final channelwise readout.  `Re` is applied only inside
each rotated channel; in particular the finite Wronskian appears unchanged. -/
theorem canonicalCompletedC3FiniteSeparatedBoundaryFinalReadout_eq
    (M : ℕ) (s : ℂ)
    (offDiagonalOrientation seamDefectOrientation :
      CanonicalCompletedC3BoundaryChannelOrientation) :
    canonicalCompletedC3SeparatedBoundaryFinalReadout
        (canonicalCompletedC3SeparatedBoundaryOrientationsWith
          offDiagonalOrientation seamDefectOrientation)
        (canonicalCompletedC3FiniteSeparatedBoundaryChannels M s) =
      canonicalCompletedC3BoundaryTraceNormalization
          (canonicalCompletedC3FiniteSeparatedBoundaryChannels M s).radialGreen +
        (canonicalCompletedC3FiniteSeparatedBoundaryChannels M s).wronskianSkew +
        canonicalCompletedC3RotatedRealChannelReadout
          offDiagonalOrientation
          (canonicalCompletedC3FiniteSeparatedBoundaryChannels M s).offDiagonal +
        canonicalCompletedC3RotatedRealChannelReadout
          seamDefectOrientation
          (canonicalCompletedC3FiniteSeparatedBoundaryChannels M s).seamDefect := by
  unfold canonicalCompletedC3SeparatedBoundaryFinalReadout
    canonicalCompletedC3SeparatedBoundaryOrientationsWith
  rw [canonicalCompletedC3RadialGreenChannelReadout_eq_normalization]
  change _ +
      canonicalCompletedC3RotatedRealChannelReadout
        canonicalCompletedC3WronskianSkewChannelOrientation
        (canonicalCompletedC3FinitePolarizedScalarBoundaryReadout M s) + _ + _ = _
  rw [canonicalCompletedC3WronskianSkewChannelReadout_finitePolarized]
  rfl

/-- The same finite decomposition after the canonical real-linear diagonal
normalization. -/
theorem canonicalCompletedC3FiniteCoupledBoundaryReadout_normalized_eq_polarized_add_seam
    (M : ℕ) (s : ℂ) :
    canonicalCompletedC3BoundaryTraceNormalization
        (canonicalCompletedC3FiniteCoupledBoundaryReadout M s) =
      canonicalCompletedC3BoundaryTraceNormalization
          (canonicalCompletedC3FinitePolarizedScalarBoundaryReadout M s) +
        canonicalCompletedC3BoundaryTraceNormalization
          (canonicalCompletedC3FinitePolarizedSeamDefect M s) := by
  rw [canonicalCompletedC3FiniteCoupledBoundaryReadout_eq_polarized_add_seam]
  simp [canonicalCompletedC3BoundaryTraceNormalization, Complex.add_re]
  ring

/-- The real-part normalization used for the raw C3 Green phase annihilates a
diagonal scalar Wronskian.  It must therefore be applied to the Green/seam
readout, not pushed through the scalar Wronskian channel. -/
theorem canonicalCompletedC3BoundaryTraceNormalization_polarizedScalar_eq_zero
    (M : ℕ) (s : ℂ) :
    canonicalCompletedC3BoundaryTraceNormalization
        (canonicalCompletedC3FinitePolarizedScalarBoundaryReadout M s) = 0 := by
  rw [canonicalCompletedC3FinitePolarizedScalarBoundaryReadout_eq_wronskian]
  unfold canonicalCompletedC3BoundaryTraceNormalization
  simp [completedGreenWronskian, Complex.mul_re]
  ring

/-- Consequently the normalized coupled ledger is exactly the normalized
readout of the independently constructed polarized seam account. -/
theorem canonicalCompletedC3FiniteCoupledBoundaryReadout_normalized_eq_seam
    (M : ℕ) (s : ℂ) :
    canonicalCompletedC3BoundaryTraceNormalization
        (canonicalCompletedC3FiniteCoupledBoundaryReadout M s) =
      canonicalCompletedC3BoundaryTraceNormalization
        (canonicalCompletedC3FinitePolarizedSeamDefect M s) := by
  rw [
    canonicalCompletedC3FiniteCoupledBoundaryReadout_normalized_eq_polarized_add_seam,
    canonicalCompletedC3BoundaryTraceNormalization_polarizedScalar_eq_zero,
    zero_add]

/-- Corrected enriched-TFVD Green boundary at the same C3 cutoff and with the
canonical Haar/trace normalization. -/
def canonicalCompletedC3FiniteCorrectedGreenReadout
    (M : ℕ) (s : ℂ) : ℂ :=
  NativeCarryC3Crosswalk.finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) s

/-- Difference between the two canonically normalized finite boundary
readouts. -/
def canonicalCompletedC3FiniteBoundarySeamDefect
    (M : ℕ) (s : ℂ) : ℂ :=
  canonicalCompletedC3BoundaryTraceNormalization
      (canonicalCompletedC3FiniteCoupledBoundaryReadout M s) -
    canonicalCompletedC3BoundaryTraceNormalization
      (canonicalCompletedC3FiniteCorrectedGreenReadout M s)

/-- Explicit infinite C3 Green bulk selected by the corrected enriched-TFVD
cutoffs. -/
def canonicalCompletedC3InfiniteCorrectedGreenBulk (s : ℂ) : ℂ :=
  ((cpRadialDifference 3 (criticalDisplacement s.re) : ℝ) : ℂ) *
    infiniteReflectedGradientPairing s

/-- Infinite value of the complete finite C3 ledger.  The first coordinate is
the completed Green bulk and the second is the chart retained by the angular
boundary account. -/
def canonicalCompletedC3InfiniteCoupledBoundaryLedger (s : ℂ) : ℂ :=
  canonicalCompletedC3InfiniteCorrectedGreenBulk s -
    bracketedDirichletChart 3 s

/-- Canonically normalized boundary trace carried by the complete C3 limit. -/
def canonicalCompletedC3NormalizedGreenLimitTrace (s : ℂ) : ℂ :=
  canonicalCompletedC3BoundaryTraceNormalization
    (canonicalCompletedC3InfiniteCorrectedGreenBulk s)

/-- Canonical diagonal normalization of the complete coupled-ledger limit. -/
def canonicalCompletedC3NormalizedCoupledBoundaryLedgerLimit
    (s : ℂ) : ℂ :=
  canonicalCompletedC3BoundaryTraceNormalization
    (canonicalCompletedC3InfiniteCoupledBoundaryLedger s)

/-- Positive radial energy underlying the normalized infinite C3 trace. -/
def canonicalCompletedC3InfiniteRadialGreenEnergy (s : ℂ) : ℝ :=
  2 * cpRadialCofactor 3 (criticalDisplacement s.re) *
    infiniteReflectedGreenEnergy s

/-- The corrected finite Green readouts converge to the explicit infinite C3
bulk before diagonal normalization. -/
theorem canonicalCompletedC3FiniteCorrectedGreenReadout_tendsto
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ => canonicalCompletedC3FiniteCorrectedGreenReadout M s)
      atTop (nhds (canonicalCompletedC3InfiniteCorrectedGreenBulk s)) := by
  have hlimit :=
    (NativeCarryC3Crosswalk.greenForm_finiteC3GenuineBracketGreenBoundaryPair_tendsto
      hs).comp tendsto_three_mul_atTop
  have hfunctions :
      (fun M : ℕ => canonicalCompletedC3FiniteCorrectedGreenReadout M s) =
        (fun M : ℕ =>
          NativeCarrySpectralWeyl.Boundary.greenForm (𝕜 := ℂ)
            (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
              (3 * M) s)
            (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
              (3 * M) (reflectedParameter s))) := by
    funext M
    exact
      NativeCarryC3Crosswalk.finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary_eq_greenForm
        M tfvdHaarScale_ne_zero (fun _ : ℕ => (1 : ℂ))
        (by intro m; norm_num) s
  rw [hfunctions]
  simpa [canonicalCompletedC3InfiniteCorrectedGreenBulk,
    Function.comp_def] using hlimit

/-- The complete finite ledger has an unconditional limit on the Genuine
strip.  Its Green coordinate completes to the radial bulk, while its explicit
angular boundary coordinate completes to the negative bracketed chart. -/
theorem canonicalCompletedC3FiniteCoupledBoundaryReadout_tendsto
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ => canonicalCompletedC3FiniteCoupledBoundaryReadout M s)
      atTop
      (nhds (canonicalCompletedC3InfiniteCoupledBoundaryLedger s)) := by
  have hgreen :=
    (NativeCarryC3Crosswalk.greenForm_finiteC3GenuineBracketGreenBoundaryPair_tendsto
      hs).comp tendsto_three_mul_atTop
  have hboundary :=
    finiteCanonicalAngularBracketCoupledBoundary_tendsto_neg_chart
      (s := s) (by linarith [hs.1])
  have hsum := hgreen.add hboundary
  have hfunctions :
      (fun M : ℕ => canonicalCompletedC3FiniteCoupledBoundaryReadout M s) =
        (fun M : ℕ =>
          NativeCarrySpectralWeyl.Boundary.greenForm (𝕜 := ℂ)
              (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
                (3 * M) s)
              (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
                (3 * M) (reflectedParameter s)) +
            finiteCanonicalAngularBracketCoupledBoundary M s) := by
    funext M
    unfold canonicalCompletedC3FiniteCoupledBoundaryReadout
      finiteCanonicalTfvdCoupledGenuineGreenFlux
    rw [NativeCarryC3Crosswalk.greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_genuineFlux]
  rw [hfunctions]
  simpa [canonicalCompletedC3InfiniteCoupledBoundaryLedger,
    canonicalCompletedC3InfiniteCorrectedGreenBulk, Function.comp_def,
    sub_eq_add_neg] using hsum

/-- The same convergence after applying the canonical diagonal boundary
normalization. -/
theorem canonicalCompletedC3FiniteCorrectedGreenReadout_normalized_tendsto
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ =>
        canonicalCompletedC3BoundaryTraceNormalization
          (canonicalCompletedC3FiniteCorrectedGreenReadout M s))
      atTop (nhds (canonicalCompletedC3NormalizedGreenLimitTrace s)) := by
  have hcontinuous :
      Continuous canonicalCompletedC3BoundaryTraceNormalization := by
    unfold canonicalCompletedC3BoundaryTraceNormalization
    fun_prop
  simpa [canonicalCompletedC3NormalizedGreenLimitTrace, Function.comp_def] using
    (hcontinuous.tendsto
      (canonicalCompletedC3InfiniteCorrectedGreenBulk s)).comp
        (canonicalCompletedC3FiniteCorrectedGreenReadout_tendsto hs)

/-- Passage of the complete ledger through the continuous diagonal boundary
normalization. -/
theorem canonicalCompletedC3FiniteCoupledBoundaryReadout_normalized_tendsto
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ =>
        canonicalCompletedC3BoundaryTraceNormalization
          (canonicalCompletedC3FiniteCoupledBoundaryReadout M s))
      atTop
      (nhds (canonicalCompletedC3NormalizedCoupledBoundaryLedgerLimit s)) := by
  have hcontinuous :
      Continuous canonicalCompletedC3BoundaryTraceNormalization := by
    unfold canonicalCompletedC3BoundaryTraceNormalization
    fun_prop
  simpa [canonicalCompletedC3NormalizedCoupledBoundaryLedgerLimit,
    Function.comp_def] using
    (hcontinuous.tendsto
      (canonicalCompletedC3InfiniteCoupledBoundaryLedger s)).comp
        (canonicalCompletedC3FiniteCoupledBoundaryReadout_tendsto hs)

/-- The normalized explicit finite seam account has the same unconditional
internally constructed limit as the normalized coupled ledger. -/
theorem canonicalCompletedC3FinitePolarizedSeamDefect_normalized_tendsto
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ =>
        canonicalCompletedC3BoundaryTraceNormalization
          (canonicalCompletedC3FinitePolarizedSeamDefect M s))
      atTop
      (nhds (canonicalCompletedC3NormalizedCoupledBoundaryLedgerLimit s)) := by
  have hlimit :=
    canonicalCompletedC3FiniteCoupledBoundaryReadout_normalized_tendsto hs
  have hfunctions :
      (fun M : ℕ =>
        canonicalCompletedC3BoundaryTraceNormalization
          (canonicalCompletedC3FinitePolarizedSeamDefect M s)) =
        (fun M : ℕ =>
          canonicalCompletedC3BoundaryTraceNormalization
            (canonicalCompletedC3FiniteCoupledBoundaryReadout M s)) := by
    funext M
    exact
      (canonicalCompletedC3FiniteCoupledBoundaryReadout_normalized_eq_seam
        M s).symm
  rw [hfunctions]
  exact hlimit

/-- The normalized C3 limit has exactly the centered spectral factor times its
positive radial energy. -/
theorem canonicalCompletedC3NormalizedGreenLimitTrace_eq_energy
    (s : ℂ) :
    canonicalCompletedC3NormalizedGreenLimitTrace s =
      (centeredHeightParameter s -
          (starRingEnd ℂ) (centeredHeightParameter s)) *
        (canonicalCompletedC3InfiniteRadialGreenEnergy s : ℂ) := by
  rw [canonicalCompletedC3NormalizedGreenLimitTrace,
    canonicalCompletedC3BoundaryTraceNormalization,
    canonicalCompletedC3InfiniteCorrectedGreenBulk,
    canonicalCompletedC3InfiniteRadialGreenEnergy,
    cpRadialDifference_eq_two_mul_delta_mul_cofactor]
  apply Complex.ext
  · simp [Complex.mul_re]
  · simp [Complex.mul_im, centeredHeightParameter_im,
      infiniteReflectedGreenEnergy, criticalDisplacement]
    ring

/-- The infinite normalized C3 energy is strictly positive throughout the open
Genuine strip. -/
theorem canonicalCompletedC3InfiniteRadialGreenEnergy_pos
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    0 < canonicalCompletedC3InfiniteRadialGreenEnergy s := by
  unfold canonicalCompletedC3InfiniteRadialGreenEnergy
  exact mul_pos
    (mul_pos (by norm_num)
      (cpRadialCofactor_pos 3 (by norm_num) (criticalDisplacement s.re)))
    (infiniteReflectedGreenEnergy_pos hs)

/-- Consequently the canonical normalized C3 limit trace cannot vanish away
from the centered real axis. -/
theorem canonicalCompletedC3NormalizedGreenLimitTrace_ne_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    canonicalCompletedC3NormalizedGreenLimitTrace s ≠ 0 := by
  rw [canonicalCompletedC3NormalizedGreenLimitTrace_eq_energy]
  apply mul_ne_zero
  · apply sub_ne_zero.mpr
    intro hconj
    apply centeredHeightParameter_im_ne_zero_of_re_ne_half hoff
    exact Complex.conj_eq_iff_im.mp hconj.symm
  · exact_mod_cast ne_of_gt
      (canonicalCompletedC3InfiniteRadialGreenEnergy_pos hs)

/-- On the Genuine kernel the chart coordinate of the complete ledger is
zero, so its normalized limit is exactly the normalized Green bulk. -/
theorem canonicalCompletedC3NormalizedCoupledBoundaryLedgerLimit_eq_green_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    canonicalCompletedC3NormalizedCoupledBoundaryLedgerLimit s =
      canonicalCompletedC3NormalizedGreenLimitTrace s := by
  have hchart : bracketedDirichletChart 3 s = 0 :=
    (bracketedDirichletChart_zero_iff_genuineContinuation_zero
      3 (by norm_num) (by norm_num) hs).2 hzero
  simp [canonicalCompletedC3NormalizedCoupledBoundaryLedgerLimit,
    canonicalCompletedC3InfiniteCoupledBoundaryLedger,
    canonicalCompletedC3NormalizedGreenLimitTrace, hchart]

/-- At a Genuine zero, the completed C3 endpoint is the whole finite sewing
defect.  It disappears after the canonical diagonal normalization as the
cutoff tends to infinity. -/
theorem canonicalCompletedC3FiniteBoundarySeamDefect_tendsto_zero_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun M : ℕ => canonicalCompletedC3FiniteBoundarySeamDefect M s)
      atTop (nhds 0) := by
  have hraw :=
    NativeCarryC3Crosswalk.finiteC3CoupledGreenFlux_sub_correctedPairBoundary_tendsto_zero_of_genuine_zero
      tfvdHaarScale_ne_zero (fun _ : ℕ => (1 : ℂ))
      (by intro m; norm_num) hs hzero
  have hre :
      Tendsto
        (fun M : ℕ =>
          (canonicalCompletedC3FiniteCoupledBoundaryReadout M s -
            canonicalCompletedC3FiniteCorrectedGreenReadout M s).re)
        atTop (nhds 0) := by
    have hre' := (Complex.continuous_re.tendsto 0).comp hraw
    change Tendsto
      (fun M : ℕ =>
        (canonicalCompletedC3FiniteCoupledBoundaryReadout M s -
          canonicalCompletedC3FiniteCorrectedGreenReadout M s).re)
      atTop (nhds 0) at hre'
    exact hre'
  have hcomplex :
      Tendsto
        (fun M : ℕ =>
          Complex.ofReal
            (canonicalCompletedC3FiniteCoupledBoundaryReadout M s -
              canonicalCompletedC3FiniteCorrectedGreenReadout M s).re)
        atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Complex.continuous_ofReal.tendsto 0).comp hre
  have hnormalized :=
    (tendsto_const_nhds.mul hcomplex :
      Tendsto
        (fun M : ℕ =>
          (-(2 : ℂ) * Complex.I) *
            Complex.ofReal
              (canonicalCompletedC3FiniteCoupledBoundaryReadout M s -
                canonicalCompletedC3FiniteCorrectedGreenReadout M s).re)
        atTop (nhds ((-(2 : ℂ) * Complex.I) * 0)))
  have hfunctions :
      (fun M : ℕ => canonicalCompletedC3FiniteBoundarySeamDefect M s) =
        (fun M : ℕ =>
          (-(2 : ℂ) * Complex.I) *
            Complex.ofReal
              (canonicalCompletedC3FiniteCoupledBoundaryReadout M s -
                canonicalCompletedC3FiniteCorrectedGreenReadout M s).re) := by
    funext M
    simp [canonicalCompletedC3FiniteBoundarySeamDefect,
      canonicalCompletedC3BoundaryTraceNormalization, Complex.sub_re]
    ring
  rw [hfunctions]
  simpa using hnormalized

/-- At a Genuine zero, the normalized coupled ledger itself converges to the
positive canonical C3 boundary trace: the vanishing seam contributes no
external boundary term. -/
theorem canonicalCompletedC3FiniteCoupledBoundaryReadout_normalized_tendsto_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun M : ℕ =>
        canonicalCompletedC3BoundaryTraceNormalization
          (canonicalCompletedC3FiniteCoupledBoundaryReadout M s))
      atTop (nhds (canonicalCompletedC3NormalizedGreenLimitTrace s)) := by
  rw [←
    canonicalCompletedC3NormalizedCoupledBoundaryLedgerLimit_eq_green_of_genuine_zero
      hs hzero]
  exact canonicalCompletedC3FiniteCoupledBoundaryReadout_normalized_tendsto hs

/-- The completed scalar Wronskian vanishes on the Genuine kernel because its
value coordinate is exactly the completed characteristic. -/
theorem canonicalCompletedC3EnrichedTfvdWronskian_eq_zero_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    completedGreenWronskian
        canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
        canonicalCompletedC3EnrichedTfvdBoundaryCompanion
        (centeredHeightParameter s) (centeredHeightParameter s) = 0 := by
  have hzStrip :
      operatorHeightParameter (centeredHeightParameter s) ∈
        genuineCriticalStrip := by
    simpa using hs
  have hzeta : riemannZeta s = 0 := by
    rwa [genuineContinuation_eq_riemannZeta hs] at hzero
  have hcharacteristic :
      completedNativeOperatorCharacteristic (centeredHeightParameter s) = 0 := by
    rw [completedNativeOperatorCharacteristic_eq_completedRiemannZeta]
    · simp [hzeta]
    · exact hzStrip
  have hvalue :
      canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
          (centeredHeightParameter s) = 0 := by
    rw [canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout_eq_characteristic
      hzStrip]
    exact hcharacteristic
  simp [completedGreenWronskian, hvalue]

/-- Concrete limit interface for the remaining global readout.  Both
sequences are fixed by the enriched TFVD/C3 construction; no auxiliary
approximants can be chosen in this proposition. -/
def CanonicalCompletedC3GlobalBoundaryLimitIntertwining : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    ∀ hoff : s.re ≠ (1 : ℝ) / 2,
      let z : ℂ := centeredHeightParameter s
      let hz : z.im ≠ 0 :=
        centeredHeightParameter_im_ne_zero_of_re_ne_half hoff
      Tendsto
          (fun M : ℕ =>
            canonicalCompletedC3BoundaryTraceNormalization
              (canonicalCompletedC3FiniteCoupledBoundaryReadout M s))
          atTop
          (nhds
            (completedGreenWronskian
              canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
              canonicalCompletedC3EnrichedTfvdBoundaryCompanion z z)) ∧
        Tendsto
          (fun M : ℕ =>
            canonicalCompletedC3BoundaryTraceNormalization
              (canonicalCompletedC3FiniteCorrectedGreenReadout M s))
          atTop
          (nhds (canonicalCompletedC3GlobalBoundaryGreenTrace z hz))

/-- The completed scalar boundary readout is the limit of the canonically
normalized coupled C3 ledger. -/
def CanonicalCompletedC3WronskianLimitIntertwining : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    ∀ _hoff : s.re ≠ (1 : ℝ) / 2,
      let z : ℂ := centeredHeightParameter s
      Tendsto
        (fun M : ℕ =>
          canonicalCompletedC3BoundaryTraceNormalization
            (canonicalCompletedC3FiniteCoupledBoundaryReadout M s))
        atTop
        (nhds
          (completedGreenWronskian
            canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
            canonicalCompletedC3EnrichedTfvdBoundaryCompanion z z))

/-- The normalized readout of the explicit finite seam account converges to
the completed Wronskian.  On the Genuine kernel the target Wronskian is zero,
so this specializes to literal no-leak. -/
def CanonicalCompletedC3ExplicitPolarizedSeamReadoutIntertwining : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    ∀ _hoff : s.re ≠ (1 : ℝ) / 2,
      let z : ℂ := centeredHeightParameter s
      Tendsto
        (fun M : ℕ =>
          canonicalCompletedC3BoundaryTraceNormalization
            (canonicalCompletedC3FinitePolarizedSeamDefect M s))
        atTop
        (nhds
          (completedGreenWronskian
            canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
            canonicalCompletedC3EnrichedTfvdBoundaryCompanion z z))

/-- The technical completed C3 scalar Green--Wronskian seam.  Its finite
decomposition is
`canonicalCompletedC3FiniteCoupledBoundaryReadout_eq_polarized_add_seam`;
this field is precisely the remaining limit statement for its explicit seam
channel. -/
def CanonicalCompletedC3ScalarGreenWronskianSeam : Prop :=
  CanonicalCompletedC3ExplicitPolarizedSeamReadoutIntertwining

/-- Because the C3 phase normalization kills the separate diagonal scalar
channel, the normalized ledger/Wronskian limit is exactly the explicit seam
readout intertwining. -/
theorem canonicalCompletedC3WronskianLimitIntertwining_iff_explicitSeamReadout :
    CanonicalCompletedC3WronskianLimitIntertwining ↔
      CanonicalCompletedC3ExplicitPolarizedSeamReadoutIntertwining := by
  constructor
  · intro hlimit s hs hoff
    dsimp only
    have h := hlimit hs hoff
    dsimp only at h
    have hfunctions :
        (fun M : ℕ =>
          canonicalCompletedC3BoundaryTraceNormalization
            (canonicalCompletedC3FiniteCoupledBoundaryReadout M s)) =
          (fun M : ℕ =>
            canonicalCompletedC3BoundaryTraceNormalization
              (canonicalCompletedC3FinitePolarizedSeamDefect M s)) := by
      funext M
      exact
        canonicalCompletedC3FiniteCoupledBoundaryReadout_normalized_eq_seam M s
    rwa [hfunctions] at h
  · intro hseam s hs hoff
    dsimp only
    have h := hseam hs hoff
    dsimp only at h
    have hfunctions :
        (fun M : ℕ =>
          canonicalCompletedC3BoundaryTraceNormalization
            (canonicalCompletedC3FinitePolarizedSeamDefect M s)) =
          (fun M : ℕ =>
            canonicalCompletedC3BoundaryTraceNormalization
              (canonicalCompletedC3FiniteCoupledBoundaryReadout M s)) := by
      funext M
      exact
        (canonicalCompletedC3FiniteCoupledBoundaryReadout_normalized_eq_seam
          M s).symm
    rwa [hfunctions] at h

theorem canonicalCompletedC3WronskianLimitIntertwining_iff_scalarSeam :
    CanonicalCompletedC3WronskianLimitIntertwining ↔
      CanonicalCompletedC3ScalarGreenWronskianSeam := by
  exact
    canonicalCompletedC3WronskianLimitIntertwining_iff_explicitSeamReadout

/-- Kernel-local no-leak statement for the explicit polarized seam channel.
Here the completed scalar Wronskian is already zero, so the correct target is
literally zero. -/
def CanonicalCompletedC3ExplicitPolarizedSeamNoLeakOnGenuineKernel : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    genuineContinuation s = 0 →
    ∀ _hoff : s.re ≠ (1 : ℝ) / 2,
      Tendsto
        (fun M : ℕ =>
          canonicalCompletedC3BoundaryTraceNormalization
            (canonicalCompletedC3FinitePolarizedSeamDefect M s))
        atTop (nhds 0)

/-- Vanishing of the explicit seam on every Genuine kernel point is exactly
the final confinement statement.  Thus this no-leak limit is the theorem's
analytic heart, not a formal consequence of Naimark completion alone. -/
theorem canonicalCompletedC3ExplicitPolarizedSeamNoLeakOnGenuineKernel_iff_finalConfinement :
    CanonicalCompletedC3ExplicitPolarizedSeamNoLeakOnGenuineKernel ↔
      NativeCarryC3Crosswalk.FinalGenuineZeroConfinement := by
  constructor
  · intro hNoLeak s hs hzero
    by_contra hoff
    have hknown :=
      canonicalCompletedC3FinitePolarizedSeamDefect_normalized_tendsto hs
    have hcloses := hNoLeak hs hzero hoff
    have hledgerZero :
        canonicalCompletedC3NormalizedCoupledBoundaryLedgerLimit s = 0 :=
      tendsto_nhds_unique hknown hcloses
    apply canonicalCompletedC3NormalizedGreenLimitTrace_ne_zero hs hoff
    rw [←
      canonicalCompletedC3NormalizedCoupledBoundaryLedgerLimit_eq_green_of_genuine_zero
        hs hzero]
    exact hledgerZero
  · intro hfinal s hs hzero hoff
    exact (hoff (hfinal hs hzero)).elim

/-- Pointwise closure statement left after the finite ledger has been
completed.  The ledger limit is constructed internally; this proposition
only identifies that fixed limit with the canonical completed Wronskian. -/
def CanonicalCompletedC3NormalizedLedgerClosesIntoWronskian : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    ∀ _hoff : s.re ≠ (1 : ℝ) / 2,
      let z : ℂ := centeredHeightParameter s
      canonicalCompletedC3NormalizedCoupledBoundaryLedgerLimit s =
        completedGreenWronskian
          canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
          canonicalCompletedC3EnrichedTfvdBoundaryCompanion z z

/-- Uniqueness of limits removes the sequence from the remaining Wronskian
interface: Wronskian convergence is exactly pointwise closure of the already
completed normalized ledger. -/
theorem canonicalCompletedC3WronskianLimitIntertwining_iff_ledgerClosure :
    CanonicalCompletedC3WronskianLimitIntertwining ↔
      CanonicalCompletedC3NormalizedLedgerClosesIntoWronskian := by
  constructor
  · intro hlimit s hs hoff
    dsimp only
    exact tendsto_nhds_unique
      (canonicalCompletedC3FiniteCoupledBoundaryReadout_normalized_tendsto hs)
      (hlimit hs hoff)
  · intro hclosure s hs hoff
    dsimp only
    have hknown :=
      canonicalCompletedC3FiniteCoupledBoundaryReadout_normalized_tendsto hs
    have hidentity := hclosure hs hoff
    dsimp only at hidentity
    simpa only [hidentity] using hknown

/-- The canonically normalized complete C3 trace passes through the canonical
camera readout to the global Hilbert Cauchy trace. -/
def CanonicalCompletedC3GlobalGreenReadoutIntertwining : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    ∀ hoff : s.re ≠ (1 : ℝ) / 2,
      let z : ℂ := centeredHeightParameter s
      let hz : z.im ≠ 0 :=
        centeredHeightParameter_im_ne_zero_of_re_ne_half hoff
      canonicalCompletedC3NormalizedGreenLimitTrace s =
        canonicalCompletedC3GlobalBoundaryGreenTrace z hz

/-- Energy-level spelling of the canonical C3-to-global Hilbert readout. -/
def CanonicalCompletedC3GlobalEnergyReadoutIntertwining : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    ∀ _hoff : s.re ≠ (1 : ℝ) / 2,
      canonicalCompletedC3InfiniteRadialGreenEnergy s =
        canonicalCompletedC3GammaEnergy (centeredHeightParameter s)

/-- Off the centered real axis, equality of the two boundary traces is exactly
equality of their positive quadratic energies. -/
theorem canonicalCompletedC3GlobalGreenReadoutIntertwining_iff_energy
    : CanonicalCompletedC3GlobalGreenReadoutIntertwining ↔
        CanonicalCompletedC3GlobalEnergyReadoutIntertwining := by
  constructor
  · intro hreadout s hs hoff
    have htrace := hreadout hs hoff
    dsimp only at htrace
    rw [canonicalCompletedC3NormalizedGreenLimitTrace_eq_energy,
      canonicalCompletedC3GlobalBoundaryGreenTrace_eq_energy] at htrace
    have hfactor :
        centeredHeightParameter s -
            (starRingEnd ℂ) (centeredHeightParameter s) ≠ 0 := by
      apply sub_ne_zero.mpr
      intro hconj
      apply centeredHeightParameter_im_ne_zero_of_re_ne_half hoff
      exact Complex.conj_eq_iff_im.mp hconj.symm
    have henergyComplex :
        (canonicalCompletedC3InfiniteRadialGreenEnergy s : ℂ) =
          (canonicalCompletedC3GammaEnergy
            (centeredHeightParameter s) : ℂ) :=
      mul_left_cancel₀ hfactor htrace
    exact_mod_cast henergyComplex
  · intro henergy s hs hoff
    dsimp only
    rw [canonicalCompletedC3NormalizedGreenLimitTrace_eq_energy,
      canonicalCompletedC3GlobalBoundaryGreenTrace_eq_energy]
    congr 1
    exact_mod_cast henergy hs hoff

/-- Expanded norm form of the same remaining global readout equality. -/
theorem canonicalCompletedC3GlobalGreenReadoutIntertwining_iff_seededGammaNorm
    : CanonicalCompletedC3GlobalGreenReadoutIntertwining ↔
        ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
          ∀ hoff : s.re ≠ (1 : ℝ) / 2,
            canonicalCompletedC3InfiniteRadialGreenEnergy s =
              ‖(NativeCarryC3Crosswalk.seededCompletedTfvdCarryGammaState
                  s hoff).fst‖ ^ 2 +
                ‖(NativeCarryC3Crosswalk.seededCompletedTfvdCarryGammaState
                  s hoff).snd‖ ^ 2 := by
  rw [canonicalCompletedC3GlobalGreenReadoutIntertwining_iff_energy]
  constructor
  · intro henergy s hs hoff
    rw [← canonicalCompletedC3GammaEnergy_centeredHeightParameter s hoff]
    exact henergy hs hoff
  · intro hnorm s hs hoff
    rw [canonicalCompletedC3GammaEnergy_centeredHeightParameter s hoff]
    exact hnorm hs hoff

/-- Since convergence of the normalized corrected Green trace is already a
theorem, the concrete two-sequence limit interface consists exactly of the
Wronskian limit and the canonical global readout equality. -/
theorem canonicalCompletedC3GlobalBoundaryLimitIntertwining_iff
    : CanonicalCompletedC3GlobalBoundaryLimitIntertwining ↔
        CanonicalCompletedC3WronskianLimitIntertwining ∧
          CanonicalCompletedC3GlobalGreenReadoutIntertwining := by
  constructor
  · intro hlimit
    constructor
    · intro s hs hoff
      exact (hlimit hs hoff).1
    · intro s hs hoff
      dsimp only
      have hknown :=
        canonicalCompletedC3FiniteCorrectedGreenReadout_normalized_tendsto hs
      have hglobal := (hlimit hs hoff).2
      exact tendsto_nhds_unique hknown hglobal
  · rintro ⟨hwronskian, hglobal⟩ s hs hoff
    dsimp only
    constructor
    · exact hwronskian hs hoff
    · have hknown :=
        canonicalCompletedC3FiniteCorrectedGreenReadout_normalized_tendsto hs
      have hreadout := hglobal hs hoff
      simpa only [hreadout] using hknown

/-- Energy-normalized decomposition of the completed-bar bridge. -/
theorem canonicalCompletedC3GlobalBoundaryLimitIntertwining_iff_wronskian_and_energy
    : CanonicalCompletedC3GlobalBoundaryLimitIntertwining ↔
        CanonicalCompletedC3WronskianLimitIntertwining ∧
          CanonicalCompletedC3GlobalEnergyReadoutIntertwining := by
  rw [canonicalCompletedC3GlobalBoundaryLimitIntertwining_iff,
    canonicalCompletedC3GlobalGreenReadoutIntertwining_iff_energy]

/-- On the Genuine kernel, the Wronskian limit interface identifies the
completed Wronskian with the already proved positive normalized C3 limit. -/
theorem canonicalCompletedC3EnrichedTfvdWronskian_eq_normalizedGreenLimit_of_limitIntertwining
    (hlimit : CanonicalCompletedC3WronskianLimitIntertwining)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    completedGreenWronskian
        canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
        canonicalCompletedC3EnrichedTfvdBoundaryCompanion
        (centeredHeightParameter s) (centeredHeightParameter s) =
      canonicalCompletedC3NormalizedGreenLimitTrace s := by
  exact tendsto_nhds_unique (hlimit hs hoff)
    (canonicalCompletedC3FiniteCoupledBoundaryReadout_normalized_tendsto_of_genuine_zero
      hs hzero)

/-- Thus the Wronskian limit identification alone is the minimal completed C3
seam needed for unconditional Genuine-zero confinement. -/
theorem finalGenuineZeroConfinement_of_wronskianLimitIntertwining
    (hlimit : CanonicalCompletedC3WronskianLimitIntertwining) :
    NativeCarryC3Crosswalk.FinalGenuineZeroConfinement := by
  intro s hs hzero
  by_contra hoff
  have hidentity :=
    canonicalCompletedC3EnrichedTfvdWronskian_eq_normalizedGreenLimit_of_limitIntertwining
      hlimit hs hzero hoff
  have hwronskian :=
    canonicalCompletedC3EnrichedTfvdWronskian_eq_zero_of_genuine_zero hs hzero
  apply canonicalCompletedC3NormalizedGreenLimitTrace_ne_zero hs hoff
  rw [← hidentity, hwronskian]

/-- Kernel-local form of the global no-leak identity.  This is the exact
surface needed for confinement; it does not demand a boundary equality away
from the zero locus. -/
def CanonicalCompletedC3GlobalBoundaryNoLeakOnGenuineKernel : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    genuineContinuation s = 0 →
    ∀ hoff : s.re ≠ (1 : ℝ) / 2,
      let z : ℂ := centeredHeightParameter s
      let hz : z.im ≠ 0 :=
        centeredHeightParameter_im_ne_zero_of_re_ne_half hoff
      completedGreenWronskian
          canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
          canonicalCompletedC3EnrichedTfvdBoundaryCompanion z z =
        canonicalCompletedC3GlobalBoundaryGreenTrace z hz

/-- Uniqueness of limits turns the normalized finite no-leak theorem into the
global Wronskian/Green identity on the Genuine kernel. -/
theorem canonicalCompletedC3GlobalBoundaryNoLeakOnGenuineKernel_of_limitIntertwining
    (hlimit : CanonicalCompletedC3GlobalBoundaryLimitIntertwining) :
    CanonicalCompletedC3GlobalBoundaryNoLeakOnGenuineKernel := by
  intro s hs hzero hoff
  dsimp only
  have hlimits := hlimit hs hoff
  dsimp only at hlimits
  have hsub := hlimits.1.sub hlimits.2
  have hseam :=
    canonicalCompletedC3FiniteBoundarySeamDefect_tendsto_zero_of_genuine_zero
      hs hzero
  have hzeroLimit :
      Tendsto
        (fun M : ℕ =>
          canonicalCompletedC3BoundaryTraceNormalization
              (canonicalCompletedC3FiniteCoupledBoundaryReadout M s) -
            canonicalCompletedC3BoundaryTraceNormalization
              (canonicalCompletedC3FiniteCorrectedGreenReadout M s))
        atTop (nhds 0) := by
    simpa [canonicalCompletedC3FiniteBoundarySeamDefect] using hseam
  exact sub_eq_zero.mp (tendsto_nhds_unique hsub hzeroLimit)

/-- The kernel-local no-leak identity and strict positivity of the global Green
trace close the public Genuine-zero confinement target. -/
theorem finalGenuineZeroConfinement_of_globalBoundaryNoLeakOnGenuineKernel
    (hNoLeak : CanonicalCompletedC3GlobalBoundaryNoLeakOnGenuineKernel) :
    NativeCarryC3Crosswalk.FinalGenuineZeroConfinement := by
  intro s hs hzero
  by_contra hoff
  have hzStrip :
      operatorHeightParameter (centeredHeightParameter s) ∈
        genuineCriticalStrip := by
    simpa using hs
  have hzIm : (centeredHeightParameter s).im ≠ 0 :=
    centeredHeightParameter_im_ne_zero_of_re_ne_half hoff
  have hwronskian :=
    canonicalCompletedC3EnrichedTfvdWronskian_eq_zero_of_genuine_zero hs hzero
  have hidentity := hNoLeak hs hzero hoff
  dsimp only at hidentity
  apply canonicalCompletedC3GlobalBoundaryGreenTrace_ne_zero hzStrip hzIm
  rw [← hidentity, hwronskian]

/-- The concrete completed-bar limit bridge therefore suffices for the final
confinement theorem. -/
theorem finalGenuineZeroConfinement_of_globalBoundaryLimitIntertwining
    (hlimit : CanonicalCompletedC3GlobalBoundaryLimitIntertwining) :
    NativeCarryC3Crosswalk.FinalGenuineZeroConfinement :=
  finalGenuineZeroConfinement_of_globalBoundaryNoLeakOnGenuineKernel
    (canonicalCompletedC3GlobalBoundaryNoLeakOnGenuineKernel_of_limitIntertwining
      hlimit)

/-- Pure Cauchy-trace formulation left after the completed enriched TFVD
value and log-jet companion have been identified. -/
def CanonicalCompletedC3EnrichedTfvdCauchyTraceCompatibility : Prop :=
  ∀ (z : ℂ), operatorHeightParameter z ∈ genuineCriticalStrip →
    ∀ hz : z.im ≠ 0,
      completedGreenWronskian
          canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
          canonicalCompletedC3EnrichedTfvdBoundaryCompanion z z =
        (-(2 : ℂ) * Complex.I) *
          (completedGammaCauchySkew
            canonicalCompletedC3SixCameraSource z hz : ℂ)

/-- The same boundary compatibility, now written through the adjoint readout
of the promoted all-bases Naimark state. -/
def CanonicalCompletedC3GlobalCameraBoundaryCompatibility : Prop :=
  ∀ (z : ℂ), operatorHeightParameter z ∈ genuineCriticalStrip →
    ∀ hz : z.im ≠ 0,
      completedGreenWronskian
          canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
          canonicalCompletedC3EnrichedTfvdBoundaryCompanion z z =
        (-(2 : ℂ) * Complex.I) *
          (completedGammaCauchySkew
            canonicalCompletedC3GlobalCameraSource z hz : ℂ)

/-- No boundary leakage means that the algebraic Wronskian and the global
Green boundary measure are the same trace. -/
def CanonicalCompletedC3GlobalBoundaryNoLeak : Prop :=
  ∀ (z : ℂ), operatorHeightParameter z ∈ genuineCriticalStrip →
    ∀ hz : z.im ≠ 0,
      completedGreenWronskian
          canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
          canonicalCompletedC3EnrichedTfvdBoundaryCompanion z z =
        canonicalCompletedC3GlobalBoundaryGreenTrace z hz

theorem canonicalCompletedC3GlobalBoundaryNoLeak_iff_compatibility :
    CanonicalCompletedC3GlobalBoundaryNoLeak ↔
      CanonicalCompletedC3GlobalCameraBoundaryCompatibility := by
  unfold CanonicalCompletedC3GlobalBoundaryNoLeak
    CanonicalCompletedC3GlobalCameraBoundaryCompatibility
    canonicalCompletedC3GlobalBoundaryGreenTrace
  simp only [canonicalCompletedC3GlobalCauchyBoundarySkew_eq_gammaCauchySkew]

/-- Passing through the global all-camera realization changes no boundary
datum. -/
theorem canonicalCompletedC3GlobalCameraBoundaryCompatibility_iff_cauchyTrace :
    CanonicalCompletedC3GlobalCameraBoundaryCompatibility ↔
      CanonicalCompletedC3EnrichedTfvdCauchyTraceCompatibility := by
  rw [CanonicalCompletedC3GlobalCameraBoundaryCompatibility,
    CanonicalCompletedC3EnrichedTfvdCauchyTraceCompatibility,
    canonicalCompletedC3GlobalCameraSource_eq_source]

/-- Once the completed companion has been proved, the enriched TFVD Cauchy
trace compatibility is literally the canonical completed C3 scalarization.
This theorem isolates the only equality not supplied by the global Naimark
realization and the value/log-jet derivative bridge. -/
theorem canonicalCompletedC3EnrichedTfvdCauchyTraceCompatibility_iff_scalarization :
    CanonicalCompletedC3EnrichedTfvdCauchyTraceCompatibility ↔
      CanonicalCompletedC3GammaCauchyStripScalarization := by
  constructor
  · intro htrace z hs hz
    simpa only [completedGreenWronskian,
      canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout_eq_characteristic
        hs,
      canonicalCompletedC3EnrichedTfvdBoundaryCompanion_eq_completedNativeOperatorBoundaryCompanion
        hs] using htrace z hs hz
  · intro hscalar z hs hz
    simpa only [completedGreenWronskian,
      canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout_eq_characteristic
        hs,
      canonicalCompletedC3EnrichedTfvdBoundaryCompanion_eq_completedNativeOperatorBoundaryCompanion
        hs] using hscalar z hs hz

/-- The Wronskian statement through the global all-camera state is exactly the
previously isolated scalar boundary-trace seam. -/
theorem canonicalCompletedC3GlobalCameraBoundaryCompatibility_iff_scalarization :
    CanonicalCompletedC3GlobalCameraBoundaryCompatibility ↔
      CanonicalCompletedC3GammaCauchyStripScalarization := by
  rw [canonicalCompletedC3GlobalCameraBoundaryCompatibility_iff_cauchyTrace,
    canonicalCompletedC3EnrichedTfvdCauchyTraceCompatibility_iff_scalarization]

/-- The geometric no-leak statement is exactly the scalar Wronskian seam. -/
theorem canonicalCompletedC3GlobalBoundaryNoLeak_iff_scalarization :
    CanonicalCompletedC3GlobalBoundaryNoLeak ↔
      CanonicalCompletedC3GammaCauchyStripScalarization := by
  rw [canonicalCompletedC3GlobalBoundaryNoLeak_iff_compatibility,
    canonicalCompletedC3GlobalCameraBoundaryCompatibility_iff_scalarization]

/-- Once the two boundary readings are identified, strict Green positivity
excludes a nonreal zero of the completed characteristic. -/
theorem completedNativeOperatorCharacteristic_ne_zero_of_globalBoundaryNoLeak
    (hNoLeak : CanonicalCompletedC3GlobalBoundaryNoLeak)
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hz : z.im ≠ 0) :
    completedNativeOperatorCharacteristic z ≠ 0 := by
  intro hzero
  have hvalue :
      canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout z = 0 := by
    rw [canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout_eq_characteristic
      hs]
    exact hzero
  have hwronskian :
      completedGreenWronskian
          canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
          canonicalCompletedC3EnrichedTfvdBoundaryCompanion z z = 0 := by
    simp [completedGreenWronskian, hvalue]
  apply canonicalCompletedC3GlobalBoundaryGreenTrace_ne_zero hs hz
  rw [← hNoLeak z hs hz, hwronskian]

/-- Geometry becomes spectral confinement after the no-leak identification;
no additional nonvanishing premise is needed. -/
theorem finalGenuineZeroConfinement_of_globalBoundaryNoLeak
    (hNoLeak : CanonicalCompletedC3GlobalBoundaryNoLeak) :
    NativeCarryC3Crosswalk.FinalGenuineZeroConfinement :=
  finalGenuineZeroConfinement_of_canonicalCompletedC3StripScalarization
    (canonicalCompletedC3GlobalBoundaryNoLeak_iff_scalarization.mp hNoLeak)

end

end CarrySelfAdjointOperator
