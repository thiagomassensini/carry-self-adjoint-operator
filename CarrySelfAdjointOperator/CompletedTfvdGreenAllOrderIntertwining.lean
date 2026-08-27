import CarrySelfAdjointOperator.CompletedGreenForwardDifferenceVectorLimit
import CarrySelfAdjointOperator.CompletedGammaTwoParameterGreenIdentity
import CarrySelfAdjointOperator.CompletedC3BracketTfvdGreenFactorization
import CarrySelfAdjointOperator.CompletedC3SymplecticNaimarkVectorLimit
import CarrySelfAdjointOperator.CompletedC3GreenFrameOrientedCarrier
import CarrySelfAdjointOperator.CompletedC3ConcreteRealAxisKernelCarrier
import CarrySelfAdjointOperator.BR2RealComplexAllOrderBridge
import NativeCarryC3Crosswalk.CompletedTfvdGreenIntertwining
import Mathlib.Tactic

/-!
# All-order completed TFVD--C3 Green intertwining

The completed TFVD ledger reconstructs the canonical finite C3 Green port at
every complex parameter.  Since this is an equality of vector-valued
functions, it survives every finite forward difference and every parity/order
component before any scalar Green or Wronskian readout is taken.

The same statement is then transported through the faithful six-camera
packing and its canonical Naimark realization.  All equalities remain
vector-valued; no zero condition, real-part projection, or spectral hypothesis
is used.
-/

open scoped Topology BigOperators lp ENNReal NNReal

namespace CarrySelfAdjointOperator

open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Infinite
open NativeCarrySpectralWeyl.Camera

noncomputable section

attribute [local instance 10000] NormedSpace.complexToReal
attribute [local instance 10000] Complex.instNormedAddCommGroup

local instance completedTfvdGreenCameraComplexInnerProductSpace :
    InnerProductSpace ℂ RealifiedCameraComplexification :=
  RealHilbertComplexification.instInnerProductSpaceComplexOfReal

local instance completedTfvdGreenNaimarkComplexInnerProductSpace :
    InnerProductSpace ℂ RealifiedNaimarkComplexification :=
  RealHilbertComplexification.instInnerProductSpaceComplexOfReal

/-- Complete C3 port reconstructed pointwise from the uncollapsed completed
TFVD ledger. -/
def canonicalCompletedTfvdGreenPortState (z : ℂ) :
    FiniteC3GreenPortCarrier 3 :=
  completedTfvdGreenLedgerC3Port z (seededCompletedTfvdGreenLedger 1 z)

/-- The ledger-derived port and the canonical bracket Green port are the same
vector-valued function, not merely equal after a scalar readout. -/
theorem canonicalCompletedTfvdGreenPortState_eq_bracketGreenPort :
    canonicalCompletedTfvdGreenPortState =
      finiteC3GenuineBracketGreenBoundaryPair 3 := by
  funext z
  exact completedTfvdGreenLedgerC3Port_seeded z

/-- Every finite forward-difference parity jet of the completed TFVD port is
literally the corresponding jet of the canonical bracket Green port. -/
theorem canonicalCompletedTfvdGreenPort_forwardDifferenceParityJet_eq_bracket
    (k : ℕ) :
    completedGreenForwardDifferenceParityJet
        canonicalCompletedTfvdGreenPortState k =
      completedGreenForwardDifferenceParityJet
        (finiteC3GenuineBracketGreenBoundaryPair 3) k := by
  rw [canonicalCompletedTfvdGreenPortState_eq_bracketGreenPort]

/-- Six-camera realization of the complete port reconstructed from the TFVD
ledger. -/
def canonicalCompletedTfvdGreenCameraState (z : ℂ) :
    CarryGammaComplexCamera :=
  c3SixCameraPacking (canonicalCompletedTfvdGreenPortState z)

/-- The packed ledger state is pointwise the packed canonical bracket state. -/
theorem canonicalCompletedTfvdGreenCameraState_eq_bracketCameraState :
    canonicalCompletedTfvdGreenCameraState =
      fun z => (c3SixCameraPacking
        (finiteC3GenuineBracketGreenBoundaryPair 3 z) :
          CarryGammaComplexCamera) := by
  funext z
  rw [canonicalCompletedTfvdGreenCameraState,
    canonicalCompletedTfvdGreenPortState_eq_bracketGreenPort]

/-- The complete all-order finite-difference identity remains true after the
faithful six-camera packing. -/
theorem canonicalCompletedTfvdGreenCamera_forwardDifferenceParityJet_eq_bracket
    (k : ℕ) :
    completedGreenForwardDifferenceParityJet
        canonicalCompletedTfvdGreenCameraState k =
      completedGreenForwardDifferenceParityJet
        (fun z => (c3SixCameraPacking
          (finiteC3GenuineBracketGreenBoundaryPair 3 z) :
            CarryGammaComplexCamera)) k := by
  rw [canonicalCompletedTfvdGreenCameraState_eq_bracketCameraState]
  rfl

/-- Canonical Naimark realization of the complete C3 port reconstructed from
the completed TFVD ledger. -/
def canonicalCompletedTfvdGreenNaimarkState (z : ℂ) :
    CarryGammaComplexNaimark :=
  c3SixCameraNaimarkRealization (canonicalCompletedTfvdGreenPortState z)

/-- The Naimark ledger state is pointwise the Naimark realization of the
canonical bracket Green port. -/
theorem canonicalCompletedTfvdGreenNaimarkState_eq_bracketNaimarkState :
    canonicalCompletedTfvdGreenNaimarkState =
      fun z => (c3SixCameraNaimarkRealization
        (finiteC3GenuineBracketGreenBoundaryPair 3 z) :
          CarryGammaComplexNaimark) := by
  funext z
  rw [canonicalCompletedTfvdGreenNaimarkState,
    canonicalCompletedTfvdGreenPortState_eq_bracketGreenPort]

/-- All parity and order components commute with the completed TFVD--bracket
identification after canonical Naimark promotion. -/
theorem canonicalCompletedTfvdGreenNaimark_forwardDifferenceParityJet_eq_bracket
    (k : ℕ) :
    completedGreenForwardDifferenceParityJet
        canonicalCompletedTfvdGreenNaimarkState k =
      completedGreenForwardDifferenceParityJet
        (fun z => (c3SixCameraNaimarkRealization
          (finiteC3GenuineBracketGreenBoundaryPair 3 z) :
            CarryGammaComplexNaimark)) k := by
  rw [canonicalCompletedTfvdGreenNaimarkState_eq_bracketNaimarkState]
  rfl

/-! ## The native real source and the all-cutoff completed carrier -/

/-- The ordinary leg of the Genuine Green port is the discrete slope of the
same real native state, after the canonical injective complex packaging. -/
theorem finiteC3GenuineBracketGreenBoundaryPair_snd_eq_packagedNativeSlope
    (M : ℕ) (time : ℝ) (n : Fin M) :
    (finiteC3GenuineBracketGreenBoundaryPair M (nativeLine time)).2 n =
      CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
        (FiniteNativeCarryOperator.Operator.nativeState time (n.val + 2) -
          FiniteNativeCarryOperator.Operator.nativeState time (n.val + 1)) := by
  rw [finiteC3GenuineBracketGreenBoundaryPair_snd_apply]
  simp [CPFormal.Analytic.Cp.positiveDirichletGradient,
    CPFormal.Analytic.Cp.natDirichletTerm,
    CPFormal.Analytic.Cp.dirichletTerm,
    NativeCarryC3Crosswalk.packaged_nativeState_eq_dirichletValue_nativeLine,
    NativeCarrySpectralWeyl.Camera.dirichletValue]

/-- Coordinate-free version of the same identity, with no finite carrier in
the statement. -/
theorem positiveDirichletGradient_nativeLine_eq_packagedNativeSlope
    (time : ℝ) (n : ℕ) :
    CPFormal.Analytic.Cp.positiveDirichletGradient (nativeLine time) n =
      CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
        (FiniteNativeCarryOperator.Operator.nativeState time (n + 2) -
          FiniteNativeCarryOperator.Operator.nativeState time (n + 1)) := by
  simpa using
    finiteC3GenuineBracketGreenBoundaryPair_snd_eq_packagedNativeSlope
      (n + 1) time (⟨n, by omega⟩ : Fin (n + 1))

/-- The logarithmic Green leg is generated by the same packaged native
samples after applying the canonical diagonal logarithmic generator and then
taking the consecutive slope. -/
theorem positiveLogDirichletGradient_nativeLine_eq_packagedNativeLogSlope
    (time : ℝ) (n : ℕ) :
    CPFormal.Analytic.Cp.positiveLogDirichletGradient (nativeLine time) n =
      (Real.log ((n + 2 : ℕ) : ℝ) : ℂ) *
          CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
            (FiniteNativeCarryOperator.Operator.nativeState time (n + 2)) -
        (Real.log ((n + 1 : ℕ) : ℝ) : ℂ) *
          CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
            (FiniteNativeCarryOperator.Operator.nativeState time (n + 1)) := by
  have hvalue (m : ℕ) :
      CPFormal.Analytic.Cp.positiveDirichletValue (nativeLine time) m =
        CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
          (FiniteNativeCarryOperator.Operator.nativeState time (m + 1)) := by
    calc
      CPFormal.Analytic.Cp.positiveDirichletValue (nativeLine time) m =
          CPFormal.Analytic.Cp.natDirichletTerm (nativeLine time) (m + 1) :=
        CPFormal.Analytic.Cp.positiveDirichletValue_eq_natDirichletTerm _ _
      _ = NativeCarrySpectralWeyl.Camera.dirichletValue
          (nativeLine time) (m + 1) := by
        simp [CPFormal.Analytic.Cp.natDirichletTerm,
          CPFormal.Analytic.Cp.dirichletTerm,
          NativeCarrySpectralWeyl.Camera.dirichletValue]
      _ = CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
          (FiniteNativeCarryOperator.Operator.nativeState time (m + 1)) :=
        (NativeCarryC3Crosswalk.packaged_nativeState_eq_dirichletValue_nativeLine
          time (m + 1)).symm
  rw [CPFormal.Analytic.Cp.positiveLogDirichletGradient,
    CPFormal.Analytic.Cp.positiveLogDirichletValue,
    CPFormal.Analytic.Cp.positiveLogDirichletValue,
    hvalue, hvalue]

/-- Finite `l2` prefix generated by consecutive packaged native samples. -/
def finitePackagedNativeSlopePrefixState
    (M : ℕ) (time : ℝ) : CPFormal.Analytic.Cp.CarryVerticalL2 :=
  CPFormal.Analytic.Cp.nativeGpreCanonicalVerticalRealization
    (∑ n ∈ Finset.range M, Finsupp.single n
      (CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
        (FiniteNativeCarryOperator.Operator.nativeState time (n + 2) -
          FiniteNativeCarryOperator.Operator.nativeState time (n + 1))))

/-- Finite `l2` log-jet prefix generated by applying the logarithmic diagonal
generator to the same native samples before taking consecutive slopes. -/
def finitePackagedNativeLogSlopePrefixState
    (M : ℕ) (time : ℝ) : CPFormal.Analytic.Cp.CarryVerticalL2 :=
  CPFormal.Analytic.Cp.nativeGpreCanonicalVerticalRealization
    (∑ n ∈ Finset.range M, Finsupp.single n
      ((Real.log ((n + 2 : ℕ) : ℝ) : ℂ) *
          CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
            (FiniteNativeCarryOperator.Operator.nativeState time (n + 2)) -
        (Real.log ((n + 1 : ℕ) : ℝ) : ℂ) *
          CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
            (FiniteNativeCarryOperator.Operator.nativeState time (n + 1))))

/-- The completed ordinary TFVD prefix on the native line is exactly the
finite packaged native-slope state. -/
theorem finitePackagedNativeSlopePrefixState_eq_completedTfvdOrdinaryPrefix
    (M : ℕ) (time : ℝ) :
    finitePackagedNativeSlopePrefixState M time =
      canonicalCompletedC3DirichletGradientPrefixState
        (nativeLine time) M := by
  ext n
  change
    (∑ i ∈ Finset.range M, Finsupp.single i
      (CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
        (FiniteNativeCarryOperator.Operator.nativeState time (i + 2) -
          FiniteNativeCarryOperator.Operator.nativeState time (i + 1)))) n =
      if n < M then
        CPFormal.Analytic.Cp.positiveDirichletGradient (nativeLine time) n
      else 0
  by_cases hn : n < M
  · simp [Finset.sum_apply, Finsupp.single_apply, hn,
      positiveDirichletGradient_nativeLine_eq_packagedNativeSlope]
  · simp [Finset.sum_apply, Finsupp.single_apply, hn]

/-- The completed log-jet TFVD prefix on the native line is exactly the
finite logarithmic-generator slope state. -/
theorem finitePackagedNativeLogSlopePrefixState_eq_completedTfvdLogJetPrefix
    (M : ℕ) (time : ℝ) :
    finitePackagedNativeLogSlopePrefixState M time =
      canonicalCompletedC3LogJetPrefixState (nativeLine time) M := by
  ext n
  change
    (∑ i ∈ Finset.range M, Finsupp.single i
      ((Real.log ((i + 2 : ℕ) : ℝ) : ℂ) *
          CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
            (FiniteNativeCarryOperator.Operator.nativeState time (i + 2)) -
        (Real.log ((i + 1 : ℕ) : ℝ) : ℂ) *
          CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
            (FiniteNativeCarryOperator.Operator.nativeState time (i + 1)))) n =
      if n < M then
        CPFormal.Analytic.Cp.positiveLogDirichletGradient (nativeLine time) n
      else 0
  by_cases hn : n < M
  · simp [Finset.sum_apply, Finsupp.single_apply, hn,
      positiveLogDirichletGradient_nativeLine_eq_packagedNativeLogSlope]
  · simp [Finset.sum_apply, Finsupp.single_apply, hn]

/-- Ordinary and log-jet native channels retained together before any Green
or scalar readout. -/
def finiteNativeGeneratedC3HilbertPrefixState
    (M : ℕ) (time : ℝ) : CanonicalCompletedC3HilbertState :=
  (finitePackagedNativeSlopePrefixState M time,
    finitePackagedNativeLogSlopePrefixState M time)

/-- Exact two-channel carrier identity between the native construction and
the completed TFVD state at every cutoff. -/
theorem finiteNativeGeneratedC3HilbertPrefixState_eq_completedTfvd
    (M : ℕ) (time : ℝ) :
    finiteNativeGeneratedC3HilbertPrefixState M time =
      canonicalCompletedC3HilbertPrefixState (nativeLine time) M := by
  apply Prod.ext
  · exact finitePackagedNativeSlopePrefixState_eq_completedTfvdOrdinaryPrefix
      M time
  · exact finitePackagedNativeLogSlopePrefixState_eq_completedTfvdLogJetPrefix
      M time

/-- The native-generated ordinary/log-jet pair converges in the same fixed
completed TFVD Hilbert carrier. -/
theorem finiteNativeGeneratedC3HilbertPrefixState_tendsto
    (time : ℝ) :
    Filter.Tendsto
      (fun M : ℕ ↦ finiteNativeGeneratedC3HilbertPrefixState M time)
      Filter.atTop
      (nhds (canonicalCompletedC3HilbertState (nativeLine time)
        (by simp [nativeLine] : 0 < (nativeLine time).re))) := by
  convert canonicalCompletedC3HilbertPrefixState_tendsto
    (by simp [nativeLine] : 0 < (nativeLine time).re) using 1
  funext M
  rw [finiteNativeGeneratedC3HilbertPrefixState_eq_completedTfvd]

/-- The two notations for the real critical line used by the native and TFVD
developments are definitionally the same complex parameter. -/
theorem nativeLine_eq_criticalLineParameter (time : ℝ) :
    nativeLine time = CPFormal.Analytic.Cp.criticalLineParameter time := by
  apply Complex.ext <;>
    simp [nativeLine, CPFormal.Analytic.Cp.criticalLineParameter]

theorem nativeLine_mem_genuineCriticalStrip (time : ℝ) :
    nativeLine time ∈ CPFormal.Analytic.Cp.genuineCriticalStrip := by
  rw [nativeLine_eq_criticalLineParameter]
  exact CPFormal.Analytic.Cp.criticalLineParameter_mem_genuineCriticalStrip time

/-- Positive finite energy of the packaged native slopes. -/
def finitePackagedNativeSlopeEnergy (M : ℕ) (time : ℝ) : ℂ :=
  ∑ n ∈ Finset.range M,
    (starRingEnd ℂ)
        (CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
          (FiniteNativeCarryOperator.Operator.nativeState time (n + 2) -
            FiniteNativeCarryOperator.Operator.nativeState time (n + 1))) *
      CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
        (FiniteNativeCarryOperator.Operator.nativeState time (n + 2) -
          FiniteNativeCarryOperator.Operator.nativeState time (n + 1))

/-- On the native line the reflected Green energy is exactly the squared
energy of the same packaged native slopes; reflection introduces no new
state. -/
theorem finiteReflectedGradientPairing_nativeLine_eq_nativeSlopeEnergy
    (M : ℕ) (time : ℝ) :
    CPFormal.Analytic.Cp.finiteReflectedGradientPairing M (nativeLine time) =
      finitePackagedNativeSlopeEnergy M time := by
  have hreflected :
      CPFormal.Analytic.Cp.reflectedParameter (nativeLine time) =
        nativeLine time := by
    rw [nativeLine_eq_criticalLineParameter,
      CPFormal.Analytic.Cp.reflectedParameter_criticalLineParameter]
  rw [CPFormal.Analytic.Cp.finiteReflectedGradientPairing,
    finitePackagedNativeSlopeEnergy, hreflected]
  apply Finset.sum_congr rfl
  intro n hn
  rw [positiveDirichletGradient_nativeLine_eq_packagedNativeSlope]

/-- Native-generated ordinary and log-jet channels after faithful Green-frame
analysis, with the precompression residual retained as a third coordinate. -/
def finiteNativeGeneratedC3OrientedGreenFramePrefixState
    (M : ℕ) (time : ℝ) : CanonicalCompletedC3OrientedGreenFrameCarrier :=
  (canonicalCompletedC3GreenFramePairIntertwiner
      (finiteNativeGeneratedC3HilbertPrefixState (3 * M) time),
    (finitePackagedNativeSlopeEnergy (3 * M) time).re •
      completedTfvdResidualGenerator)

/-- Exact three-channel identity before completion: the native-generated
state is the canonical oriented TFVD/Green-frame state. -/
theorem finiteNativeGeneratedC3OrientedGreenFramePrefixState_eq_tfvd
    (M : ℕ) (time : ℝ) :
    finiteNativeGeneratedC3OrientedGreenFramePrefixState M time =
      canonicalCompletedC3OrientedGreenFramePrefixState M
        (nativeLine time) := by
  apply Prod.ext
  · rw [finiteNativeGeneratedC3OrientedGreenFramePrefixState,
      canonicalCompletedC3OrientedGreenFramePrefixState_fst,
      finiteNativeGeneratedC3HilbertPrefixState_eq_completedTfvd]
  · rw [finiteNativeGeneratedC3OrientedGreenFramePrefixState,
      canonicalCompletedC3OrientedGreenFramePrefixState_snd,
      finiteReflectedGradientPairing_nativeLine_eq_nativeSlopeEnergy]

/-- The full separated native-generated carrier, including residual, converges
to the existing completed oriented TFVD/Green-frame state. -/
theorem finiteNativeGeneratedC3OrientedGreenFramePrefixState_tendsto
    (time : ℝ) :
    Filter.Tendsto
      (fun M : ℕ ↦
        finiteNativeGeneratedC3OrientedGreenFramePrefixState M time)
      Filter.atTop
      (nhds (canonicalCompletedC3OrientedGreenFrameState
        (nativeLine time)
        (nativeLine_mem_genuineCriticalStrip time))) := by
  apply (canonicalCompletedC3OrientedGreenFramePrefixState_tendsto
    (nativeLine_mem_genuineCriticalStrip time)).congr'
  filter_upwards [] with M
  exact (finiteNativeGeneratedC3OrientedGreenFramePrefixState_eq_tfvd M time).symm

/-- Canonical inclusion of the separated oriented carrier into the concrete
complex positive carrier used by the HP route.  The residual is complexified
only here, after remaining a distinct real coordinate through completion. -/
def completedC3OrientedGreenFrameToPositiveCarrier
    (state : CanonicalCompletedC3OrientedGreenFrameCarrier) :
    CanonicalCompletedC3RealAxisPositiveCarrier :=
  let source := canonicalCompletedC3GreenFramePairSynthesis state.1
  WithLp.toLp 2
    (canonicalCompletedGreenFrameParsevalAnalysis source.1,
      WithLp.toLp 2
        (canonicalCompletedGreenFrameParsevalAnalysis source.2,
          RealHilbertComplexification.mk (WithLp.toLp 2 state.2) 0))

/-- The concrete positive HP state is exactly the canonical image of the
completed native-generated ordinary/log-jet/residual state. -/
theorem completedC3OrientedGreenFrameToPositiveCarrier_nativeLine_eq_positiveState
    (time : ℝ) :
    completedC3OrientedGreenFrameToPositiveCarrier
        (canonicalCompletedC3OrientedGreenFrameState
          (nativeLine time) (nativeLine_mem_genuineCriticalStrip time)) =
      canonicalCompletedC3RealAxisPositiveState (time : ℂ) := by
  simp only [canonicalCompletedC3RealAxisPositiveState,
    canonicalCompletedC3RealAxisOrdinaryState,
    canonicalCompletedC3RealAxisLogJetState,
    canonicalCompletedC3RealAxisComplexResidualState,
    canonicalCompletedC3RealAxisResidualState,
    Complex.ofReal_re,
    operatorHeightParameter_ofReal_eq_nativeLine]
  unfold completedC3OrientedGreenFrameToPositiveCarrier
    canonicalCompletedC3OrientedGreenFrameState
  rw [canonicalCompletedC3GreenFramePairSynthesis_intertwiner]

/-- On the native line the radial normalization is exactly one, so both
coordinates of the Genuine Green port are produced by the same real native
slope through the canonical complex packaging. -/
theorem finiteC3GenuineBracketGreenBoundaryPair_nativeLine_components_eq_packagedNativeSlope
    (M : ℕ) (time : ℝ) (n : Fin M) :
    let slope :=
      CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
        (FiniteNativeCarryOperator.Operator.nativeState time (n.val + 2) -
          FiniteNativeCarryOperator.Operator.nativeState time (n.val + 1))
    (finiteC3GenuineBracketGreenBoundaryPair M (nativeLine time)).1 n = slope ∧
      (finiteC3GenuineBracketGreenBoundaryPair M (nativeLine time)).2 n = slope := by
  dsimp only
  constructor
  · have hprefix :
        canonicalCompletedC3DirichletGradientPrefixState
            (nativeLine time) M n =
          CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
            (FiniteNativeCarryOperator.Operator.nativeState time (n.val + 2) -
              FiniteNativeCarryOperator.Operator.nativeState time (n.val + 1)) := by
      rw [← finiteC3GenuineBracketGreenBoundaryPair_snd_eq_completedPrefix]
      exact finiteC3GenuineBracketGreenBoundaryPair_snd_eq_packagedNativeSlope
        M time n
    rw [finiteC3GenuineBracketGreenBoundaryPair_fst_eq_radial_mul_completedPrefix,
      hprefix]
    simp [CPFormal.Analytic.Cp.criticalDisplacement, nativeLine]
  · exact finiteC3GenuineBracketGreenBoundaryPair_snd_eq_packagedNativeSlope
      M time n

/-- The duplicated packaged native slope, retained as a two-leg Green port. -/
def finitePackagedNativeSlopeGreenPort (M : ℕ) (time : ℝ) :
    FiniteC3GreenPortCarrier M :=
  let slope := fun n : Fin M ↦
    CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
      (FiniteNativeCarryOperator.Operator.nativeState time (n.val + 2) -
        FiniteNativeCarryOperator.Operator.nativeState time (n.val + 1))
  (WithLp.toLp 2 slope, WithLp.toLp 2 slope)

/-- Exact finite vector identity: the Genuine bracket port on the native line
is generated by the real native slope in both Green legs. -/
theorem finiteC3GenuineBracketGreenBoundaryPair_nativeLine_eq_nativeSlopePort
    (M : ℕ) (time : ℝ) :
    finiteC3GenuineBracketGreenBoundaryPair M (nativeLine time) =
      finitePackagedNativeSlopeGreenPort M time := by
  apply Prod.ext
  · ext n
    exact
      (finiteC3GenuineBracketGreenBoundaryPair_nativeLine_components_eq_packagedNativeSlope
        M time n).1
  · ext n
    exact
      (finiteC3GenuineBracketGreenBoundaryPair_nativeLine_components_eq_packagedNativeSlope
        M time n).2

/-- At cutoff `M`, the complete enriched TFVD state is read through its Green
port and promoted by the all-cutoff symplectic Naimark realization. -/
def canonicalCompletedTfvdGreenAllCutoffNaimarkState
    (M : ℕ) (s : ℂ) : RealifiedNaimarkComplexification :=
  finiteC3SymplecticNaimarkRealization (M * 3)
    (canonicalC3BracketTfvdCompletionState M s).greenPort

/-- The all-cutoff TFVD/Naimark state is exactly the realization of the
Genuine bracket port at the same cutoff. -/
theorem canonicalCompletedTfvdGreenAllCutoffNaimarkState_eq_bracket
    (M : ℕ) (s : ℂ) :
    canonicalCompletedTfvdGreenAllCutoffNaimarkState M s =
      finiteC3SymplecticNaimarkRealization (M * 3)
        (finiteC3GenuineBracketGreenBoundaryPair (M * 3) s) := by
  rw [canonicalCompletedTfvdGreenAllCutoffNaimarkState,
    canonicalC3BracketTfvdCompletionState_greenPort_eq_bracket]

/-- On the native line the all-cutoff TFVD/Naimark vector is produced
directly by the duplicated packaged slope of the real native operator. -/
theorem canonicalCompletedTfvdGreenAllCutoffNaimarkState_nativeLine_eq_nativeSlope
    (M : ℕ) (time : ℝ) :
    canonicalCompletedTfvdGreenAllCutoffNaimarkState M (nativeLine time) =
      finiteC3SymplecticNaimarkRealization (M * 3)
        (finitePackagedNativeSlopeGreenPort (M * 3) time) := by
  rw [canonicalCompletedTfvdGreenAllCutoffNaimarkState_eq_bracket,
    finiteC3GenuineBracketGreenBoundaryPair_nativeLine_eq_nativeSlopePort]

/-- The genuine/TFVD Naimark prefixes converge as vectors in one fixed global
Hilbert carrier.  This is the all-cutoff promotion, not a scalar Green limit. -/
theorem canonicalCompletedTfvdGreenAllCutoffNaimarkState_tendsto
    {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto
      (fun M : ℕ ↦ canonicalCompletedTfvdGreenAllCutoffNaimarkState M s)
      Filter.atTop
      (nhds (completedC3SymplecticNaimarkState s hs)) := by
  convert canonicalC3AllCutoffGenuineSymplecticNaimarkRealization_tendsto hs using 1
  funext M
  rw [canonicalCompletedTfvdGreenAllCutoffNaimarkState_eq_bracket,
    Nat.mul_comm M 3]

/-- Real-height specialization of the all-cutoff TFVD/Genuine carrier.  The
complex argument is only a wrapper for the real sampling grids used by the
completed forward differences. -/
def canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisPrefixState
    (M : ℕ) (z : ℂ) : RealifiedNaimarkComplexification :=
  canonicalCompletedTfvdGreenAllCutoffNaimarkState M
    (operatorHeightParameter (z.re : ℂ))

/-- Completed real-height TFVD/Genuine Naimark state. -/
def canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisState
    (z : ℂ) : RealifiedNaimarkComplexification :=
  completedC3SymplecticNaimarkState
    (operatorHeightParameter (z.re : ℂ))
    (ofReal_mem_completedNativeHeightDomain z.re).1

/-- The same all-cutoff real-height prefixes written purely from the native
real slope before canonical complex packaging and Naimark promotion. -/
def canonicalNativeSlopeAllCutoffNaimarkRealAxisPrefixState
    (M : ℕ) (z : ℂ) : RealifiedNaimarkComplexification :=
  finiteC3SymplecticNaimarkRealization (M * 3)
    (finitePackagedNativeSlopeGreenPort (M * 3) z.re)

/-- Exact pointwise identification of the native-slope and completed TFVD
prefix vectors in the fixed global Naimark carrier. -/
theorem canonicalNativeSlopeAllCutoffNaimarkRealAxisPrefixState_eq_tfvd
    (M : ℕ) :
    canonicalNativeSlopeAllCutoffNaimarkRealAxisPrefixState M =
      canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisPrefixState M := by
  funext z
  rw [canonicalNativeSlopeAllCutoffNaimarkRealAxisPrefixState,
    canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisPrefixState,
    operatorHeightParameter_ofReal_eq_nativeLine,
    canonicalCompletedTfvdGreenAllCutoffNaimarkState_nativeLine_eq_nativeSlope]

/-- Pointwise cutoff convergence on every real-height sampling point. -/
theorem canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisPrefixState_tendsto
    (z : ℂ) :
    Filter.Tendsto
      (fun M : ℕ ↦
        canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisPrefixState M z)
      Filter.atTop
      (nhds (canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisState z)) := by
  exact canonicalCompletedTfvdGreenAllCutoffNaimarkState_tendsto
    (ofReal_mem_completedNativeHeightDomain z.re).1

/-- The native real slopes themselves converge after the canonical
R-to-C packaging and all-cutoff Naimark realization. -/
theorem canonicalNativeSlopeAllCutoffNaimarkRealAxisPrefixState_tendsto
    (z : ℂ) :
    Filter.Tendsto
      (fun M : ℕ ↦
        canonicalNativeSlopeAllCutoffNaimarkRealAxisPrefixState M z)
      Filter.atTop
      (nhds (canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisState z)) := by
  convert
    canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisPrefixState_tendsto z
      using 1
  funext M
  rw [canonicalNativeSlopeAllCutoffNaimarkRealAxisPrefixState_eq_tfvd]

/-- Every parity and forward-difference order passes through the same
all-cutoff vector limit.  Both Naimark quadratures remain in the target. -/
theorem canonicalCompletedTfvdGreenAllCutoffNaimark_forwardDifferenceParityJet_tendsto
    (k : ℕ) (i : ℕ ⊕ ℕ) :
    Filter.Tendsto
      (fun M : ℕ ↦ completedGreenForwardDifferenceParityJet
        (canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisPrefixState M) k i)
      Filter.atTop
      (nhds (completedGreenForwardDifferenceParityJet
        canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisState k i)) := by
  cases i with
  | inl n =>
      unfold completedGreenForwardDifferenceParityJet
        completedGreenForwardDifferenceJet
      exact (completedGreenForwardDifference_iter_tendsto_of_pointwise
        Filter.atTop
        canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisPrefixState
        canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisState
        canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisPrefixState_tendsto
        (canonicalGreenJetStep k) (2 * n) 0).const_smul
          (((Nat.factorial (2 * n) : ℂ) *
            canonicalGreenJetStep k ^ (2 * n))⁻¹)
  | inr n =>
      unfold completedGreenForwardDifferenceParityJet
        completedGreenForwardDifferenceJet
      exact (completedGreenForwardDifference_iter_tendsto_of_pointwise
        Filter.atTop
        canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisPrefixState
        canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisState
        canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisPrefixState_tendsto
        (canonicalGreenJetStep k) (2 * n + 1) 0).const_smul
          (((Nat.factorial (2 * n + 1) : ℂ) *
            canonicalGreenJetStep k ^ (2 * n + 1))⁻¹)

/-- All parity/order finite differences of the packaged native-slope vectors
converge to the same completed TFVD/Genuine Naimark jet. -/
theorem canonicalNativeSlopeAllCutoffNaimark_forwardDifferenceParityJet_tendsto
    (k : ℕ) (i : ℕ ⊕ ℕ) :
    Filter.Tendsto
      (fun M : ℕ ↦ completedGreenForwardDifferenceParityJet
        (canonicalNativeSlopeAllCutoffNaimarkRealAxisPrefixState M) k i)
      Filter.atTop
      (nhds (completedGreenForwardDifferenceParityJet
        canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisState k i)) := by
  convert
    canonicalCompletedTfvdGreenAllCutoffNaimark_forwardDifferenceParityJet_tendsto
      k i using 1
  funext M
  rw [canonicalNativeSlopeAllCutoffNaimarkRealAxisPrefixState_eq_tfvd]

end

end CarrySelfAdjointOperator
