import CarrySelfAdjointOperator.PrimeDepthAllOrderMomentBridge
import CarrySelfAdjointOperator.MultibaseTfvdCameraGramHilbertTransport
import CarrySelfAdjointOperator.CanonicalC3SixCameraSource
import CarrySelfAdjointOperator.CompletedC3ConcretePositiveSewingClosure
import Mathlib.Tactic

/-!
# Audit of the six-source TFVD to finite-camera promotion seam

The material six-source construction has a genuinely vector-valued source
before its corrected scalar readout: ordinary and log-jet TFVD analyses at
`z`, `w`, and reflected `z`. The historical finite-camera Parseval route has
a different external index: the two geometric C3 legs, each with three camera
slots. These two six-element index types are intentionally kept distinct.
No enumeration identifies a source role with a camera slot.

The channelwise reconstruction and finite restriction can be reused once a
provenance-aware map from six analyzed roles to camera-resolved analyses is
supplied. The source construction currently supplies neither that map nor a
real-linear BR2-incidence lift into the six-role analysis datum. This file
names both missing arrows, but introduces no scalar readout, moment, Hankel
matrix, or positivity premise.
-/

open scoped InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Boundary
open NativeCarryC3Crosswalk

noncomputable section

/-! ## The two unrelated six-element index types -/

/-- The parameter provenance of one of the six TFVD source analyses. -/
inductive CanonicalC3SixSourceParameterRole
  | z
  | w
  | reflectedZ
  deriving DecidableEq, Fintype

/-- The ordered vertical channel retained at each source parameter. -/
inductive CanonicalC3SixSourceChannelRole
  | ordinary
  | logJet
  deriving DecidableEq, Fintype

/-- The material roles are parameter provenance times ordinary/log-jet
provenance. They are not camera labels. -/
abbrev CanonicalC3SixSourceRole :=
  CanonicalC3SixSourceParameterRole × CanonicalC3SixSourceChannelRole

/-- Expose the nested six-analysis datum as a family indexed by its actual
source roles. -/
def canonicalC3SixSourceRoleAnalysis
    (S : Finset NativeGpreBoundaryContext)
    (data : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) :
    CanonicalC3SixSourceRole → NativeGpreFiniteTfvdAnalysisCarrier S
  | (.z, .ordinary) => data.1.1
  | (.z, .logJet) => data.1.2
  | (.w, .ordinary) => data.2.1.1
  | (.w, .logJet) => data.2.1.2
  | (.reflectedZ, .ordinary) => data.2.2.1
  | (.reflectedZ, .logJet) => data.2.2.2

/-- Repack a source-role family into the established six-analysis datum. -/
def canonicalC3SixSourceRoleAnalysisData
    (S : Finset NativeGpreBoundaryContext)
    (roles : CanonicalC3SixSourceRole → NativeGpreFiniteTfvdAnalysisCarrier S) :
    CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S :=
  ((roles (.z, .ordinary), roles (.z, .logJet)),
    ((roles (.w, .ordinary), roles (.w, .logJet)),
      (roles (.reflectedZ, .ordinary), roles (.reflectedZ, .logJet))))

/-- The role view neither contracts nor reorders the six analyses. -/
theorem canonicalC3SixSourceRoleAnalysisData_roleAnalysis
    (S : Finset NativeGpreBoundaryContext)
    (data : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) :
    canonicalC3SixSourceRoleAnalysisData S
      (canonicalC3SixSourceRoleAnalysis S data) = data := by
  rcases data with ⟨⟨zOrdinary, zLogJet⟩,
    ⟨⟨wOrdinary, wLogJet⟩, ⟨reflectedZOrdinary, reflectedZLogJet⟩⟩⟩
  rfl

/-- Conversely, all six source-role values survive the repacking. -/
theorem canonicalC3SixSourceRoleAnalysis_roleAnalysisData
    (S : Finset NativeGpreBoundaryContext)
    (roles : CanonicalC3SixSourceRole → NativeGpreFiniteTfvdAnalysisCarrier S) :
    canonicalC3SixSourceRoleAnalysis S
      (canonicalC3SixSourceRoleAnalysisData S roles) = roles := by
  funext role
  rcases role with ⟨parameter, channel⟩
  cases parameter <;> cases channel <;> rfl

/-- The geometric leg of a slot in the historical C3 six-camera packing. -/
inductive CanonicalC3SixCameraLeg
  | first
  | second
  deriving DecidableEq, Fintype

/-- A historical camera slot is a C3 leg plus one of its three coordinates.
This type remains distinct from `CanonicalC3SixSourceRole`. -/
abbrev CanonicalC3SixCameraSlot := CanonicalC3SixCameraLeg × Fin 3

/-- The literal native camera label of each historical six-camera slot. -/
def canonicalC3SixCameraSlotLabel : CanonicalC3SixCameraSlot → ℕ
  | (.first, i) => firstC3CameraIndex i
  | (.second, i) => secondC3CameraIndex i

@[simp] theorem canonicalC3SixCameraSlotLabel_first (i : Fin 3) :
    canonicalC3SixCameraSlotLabel (.first, i) = firstC3CameraIndex i :=
  rfl

@[simp] theorem canonicalC3SixCameraSlotLabel_second (i : Fin 3) :
    canonicalC3SixCameraSlotLabel (.second, i) = secondC3CameraIndex i :=
  rfl

/-! ## The exact channelwise promotion interface -/

/-- The missing provenance-aware arrow. Its source is the six-role TFVD
analysis datum and its target is an external camera-labelled family of TFVD
analyses. It does not identify source roles with camera slots. -/
abbrev CanonicalC3SixSourceToCameraChannelAnalysis
    (S : Finset NativeGpreBoundaryContext) :=
  CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S →ₗ[ℂ]
    (ℕ →₀ NativeGpreFiniteTfvdAnalysisCarrier S)

/-- The other missing arrow: a BR2 incidence lift into the still-separated
six source roles. -/
abbrev BR2IncidenceToCanonicalC3SixSourceAnalysis
    (S : Finset NativeGpreBoundaryContext) :=
  (ℕ →₀ ℝ) →ₗ[ℝ] CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S

/-- Channelwise reconstruction without `cameraChannelSynthesis`. -/
def canonicalC3SixSourceCameraResolvedOfPromotion
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (promotion : CanonicalC3SixSourceToCameraChannelAnalysis S) :
    CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S →ₗ[ℂ]
      CameraResolvedCarryVertical :=
  (cameraChannelTfvdReconstruction q hq0 hq1 S).comp promotion

/-- Restrict the reconstructed channel family to the historical two-leg,
three-coordinate camera atlas. This is a type-correct restriction only; it
does not choose a source-role-to-camera-slot bijection. -/
def canonicalC3SixSourceFiniteCameraFamilyOfPromotion
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (promotion : CanonicalC3SixSourceToCameraChannelAnalysis S) :
    CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S →ₗ[ℂ]
      FiniteHilbertFamily CanonicalC3SixCameraSlot
        CanonicalCompletedTfvdGreenHilbertCarrier :=
  (restrictCameraResolvedCarryVertical canonicalC3SixCameraSlotLabel).comp
    (canonicalC3SixSourceCameraResolvedOfPromotion q hq0 hq1 S promotion)

/-- Coordinate formula for the reusable reconstruction/restriction tail.
Every slot is reconstructed independently from the promoted analysis at its
geometric native camera label; no synthesis occurs here. -/
theorem canonicalC3SixSourceFiniteCameraFamilyOfPromotion_apply
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (promotion : CanonicalC3SixSourceToCameraChannelAnalysis S)
    (data : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S)
    (slot : CanonicalC3SixCameraSlot) :
    (canonicalC3SixSourceFiniteCameraFamilyOfPromotion
      q hq0 hq1 S promotion data).ofLp slot =
      nativeGpreFiniteTfvdReconstruction q hq0 hq1 S
        (promotion data (canonicalC3SixCameraSlotLabel slot)) := by
  rfl

/-- Compose both missing arrows into the real-linear finite-camera input
expected by the incidence-restricted Parseval interface. Metric preservation
and visible-coefficient realization remain substantive future obligations. -/
def br2CanonicalC3SixSourceFiniteCameraIncidenceMap
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (incidenceLift : BR2IncidenceToCanonicalC3SixSourceAnalysis S)
    (promotion : CanonicalC3SixSourceToCameraChannelAnalysis S) :
    (ℕ →₀ ℝ) →ₗ[ℝ]
      FiniteHilbertFamily CanonicalC3SixCameraSlot
        CanonicalCompletedTfvdGreenHilbertCarrier :=
  ((canonicalC3SixSourceFiniteCameraFamilyOfPromotion
    q hq0 hq1 S promotion).restrictScalars ℝ).comp incidenceLift

/-! ## What the existing vector bridges do and do not provide -/

/-- Lossless reconstruction produces the same three-source Hilbert vector as
the oriented Green-frame source, before every scalar corrected readout. -/
theorem nativeC3SeededClockTfvdSixSource_vectorCrosswalk
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (z w : ℂ) :
    nativeC3SeededClockTfvdSixSourceReconstructedState
        M q hqpos.le hq1 S z w =
      CanonicalC3AllCutoffMixedOrientedGreenFrameSourceHilbert.recoveredHilbertSource
        (canonicalC3AllCutoffMixedOrientedGreenFramePrefixState M z w) :=
  nativeC3SeededClockTfvdSixSourceReconstructedState_eq_orientedGreenFrame
    M q hqpos hq1 S z w

/-- The immediate post-reconstruction vector pair used by the corrected
boundary has Green-port type, not finite-camera-family type. -/
def canonicalC3SixSourceRecoveredGreenPorts
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (data : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) :
    FiniteC3GreenPortCarrier (3 * M) × FiniteC3GreenPortCarrier (3 * M) :=
  (canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort M z w q hq0 hq1 S data,
    canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort M z w q hq0 hq1 S data)

/-- The corrected boundary is a Green/symplectic scalar functional of the
two recovered ports. It is not asserted to be a Hilbert inner product. -/
theorem canonicalC3SixSourceRecoveredGreenPorts_correctedBoundary
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (data : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) :
    canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary
      M z w q hq0 hq1 S data =
      greenForm (𝕜 := ℂ)
        (canonicalC3SixSourceRecoveredGreenPorts M z w q hq0 hq1 S data).1
        (canonicalC3SixSourceRecoveredGreenPorts M z w q hq0 hq1 S data).2 :=
  rfl

/-- Nearby no-go: the constructed oriented-to-positive carrier has a named
nonzero central sewing defect in its fixed metric. It cannot replace the
missing finite-camera visible channel. -/
theorem canonicalC3FixedPositiveCarrier_not_sixSourceSewing :
    ¬ CanonicalCompletedC3ConcreteRealAxisPositiveSewing :=
  not_canonicalCompletedC3ConcreteRealAxisPositiveSewing_of_defect

/-- Exact low-order obstruction for that fixed positive metric.  This is a
defect of a nearby oriented-vector candidate, not a claim about the missing
finite-camera promotion defined above. -/
theorem canonicalC3FixedPositiveCarrier_centralDefect_ne_zero
    (M : ℕ) :
    canonicalCompletedC3ConcretePositiveSewingDefect M 0 0 ≠ 0 :=
  canonicalCompletedC3ConcretePositiveSewingDefect_zero_zero_ne_zero M

end

end CarrySelfAdjointOperator
