import CarrySelfAdjointOperator.CompletedNativeHolomorphicGreenNontrivialWitness
import CarrySelfAdjointOperator.CompletedNativeCausalGreenProvenance
import CarrySelfAdjointOperator.CompletedC3CentralLedgerCollisionAudit
import CarrySelfAdjointOperator.CompletedC3FinalReadoutKernelBridge
import CarrySelfAdjointOperator.CompletedNativeGeometryHeightProvenance
import CarrySelfAdjointOperator.CompletedNativeTfvdEnrichedLowOrderMomentTest

/-!
# Genealogy from holomorphic Green polarization to native moments

This file records the first downstream audit after the nontrivial
camera-resolved holomorphic Green first jet.

## Existing downstream genealogy

* `holomorphicGreenPort` -> `finiteC3HolomorphicGenuineGreenBoundaryPair`:
  **CLOSED**, on the literal finite prefix.
* holomorphic camera ports -> canonical holomorphic ports -> sewn finite
  camera-pair Green form: **CLOSED**, by finite linearity of the first-leg
  eigenvalue dress.
* independent-reflected holomorphic camera kernel -> historical causal
  four-corner Green cell: **MISSING**.  The latter is a different, explicitly
  radial/reflected presentation: it uses `reflectedParameter` and
  `canonicalC3MixedRadialCoefficient`.
* historical four-corner cell -> literal prefix inner product -> reflected
  ordinary/log-jet reconstruction: **CLOSED**.
* historical four-corner Green component -> completed scalar readout:
  **MISSING AS AN ISOLATED COMPONENT**.  The completed ledger retains
  provenance, off-diagonal, residual, tail, and archimedean channels.
* fixed-center completed ledger first variation -> `h₀`: **CLOSED**.
* final real-axis scalar readout -> `dslope` -> polarized moments:
  **CLOSED**.
* a Green moment-kernel certificate plus incidence transport -> finite
  Hankel/Jacobi/height construction: **CLOSED CONDITIONALLY**.

The old `canonicalCompletedNativeTfvdEnrichedTaylorRawJet` route is not used.
Its zeroth Gram/moment equation is formally refuted by
`not_hasPolarizedCoefficientVectorEquation_enrichedTfvdTaylor`.

Consequently this module does not identify a discrete second difference with a
complex derivative, does not identify the new holomorphic kernel with a
radial-normalized scalar readout, and does not erase the completed ledger
channels.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite
open FiniteNativeCarryOperator.Camera
open Filter

noncomputable section
set_option autoImplicit false

/-! ## Historical four-corner pre-Hankel cell -/

/-- The historical causal four-corner Green component before scalar sewing.
It deliberately retains the reflected parameter and the historical Genuine
bracket ports. -/
def canonicalCompletedNativeHistoricalFourCornerGreenComponent
    (M : ℕ) (z w : ℂ) : ℂ :=
  greenForm (𝕜 := ℂ)
    (finiteC3GenuineBracketGreenBoundaryPair M w)
    (finiteC3GenuineBracketGreenBoundaryPair M (reflectedParameter z))

/-- The new name for the holomorphic port agrees exactly with the historical
holomorphic finite Green port on a canonical prefix.  This is a port-level
identity; it does not identify that port with the radial/reflected
four-corner component below. -/
theorem canonicalC3HolomorphicGreenPort_eq_historicalHolomorphicPrefix
    (M : ℕ) (s : ℂ) :
    holomorphicGreenPort M s (canonicalCompletedC3HilbertPrefixState s M) =
      finiteC3HolomorphicGenuineGreenBoundaryPair M s :=
  holomorphicGreenPort_prefix_eq_finiteC3HolomorphicGenuineGreenBoundaryPair M s

/-- Dressing one Green leg by a fixed scalar commutes with a finite port sum.
This is the only linearity needed to promote the already-established
undressed camera synthesis to the holomorphic port layer. -/
theorem radialGreenDress_finset_sum
    {N : ℕ} (rho : ℂ) (cameras : Finset ℕ)
    (port : ℕ → FiniteC3GreenPortCarrier N) :
    radialGreenDress rho (∑ camera ∈ cameras, port camera) =
      ∑ camera ∈ cameras, radialGreenDress rho (port camera) := by
  apply Prod.ext
  · have hport := map_sum (AddMonoidHom.fst _ _) port cameras
    have hdress := map_sum (AddMonoidHom.fst _ _)
      (fun camera => radialGreenDress rho (port camera)) cameras
    change rho • (AddMonoidHom.fst _ _ (∑ camera ∈ cameras, port camera)) =
      AddMonoidHom.fst _ _
        (∑ camera ∈ cameras, radialGreenDress rho (port camera))
    rw [hport, hdress]
    simpa [radialGreenDress] using (Finset.smul_sum :
      rho • ∑ camera ∈ cameras, (port camera).1 =
        ∑ camera ∈ cameras, rho • (port camera).1)
  · have hport := map_sum (AddMonoidHom.snd _ _) port cameras
    have hdress := map_sum (AddMonoidHom.snd _ _)
      (fun camera => radialGreenDress rho (port camera)) cameras
    change AddMonoidHom.snd _ _ (∑ camera ∈ cameras, port camera) =
      AddMonoidHom.snd _ _
        (∑ camera ∈ cameras, radialGreenDress rho (port camera))
    rw [hport, hdress]
    simp [radialGreenDress]

/-! ## Camera synthesis at the holomorphic port layer -/

/-- Canonical direct Green port retaining the holomorphic C3 eigenvalue. -/
def canonicalC3IndependentReflectedHolomorphicDirectGreenPort
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    FiniteC3GreenPortCarrier (3 * M) :=
  holomorphicGreenPort (3 * M) (operatorHeightParameter 0)
    (canonicalC3IndependentReflectedSixSourceReconstruction M q hq0 hq1 S u v).wSource

/-- Canonical reflected Green port retaining the holomorphic C3 eigenvalue
at the independent reflected coordinate. -/
def canonicalC3IndependentReflectedHolomorphicReflectedGreenPort
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    FiniteC3GreenPortCarrier (3 * M) :=
  holomorphicGreenPort (3 * M) (operatorHeightParameter v)
    (canonicalC3IndependentReflectedSixSourceReconstruction M q hq0 hq1 S u v).reflectedZSource

/-- The fixed camera atlas synthesizes exactly to the canonical holomorphic
direct port. -/
theorem cameraResolvedIndependentReflectedHolomorphicDirectGreenPort_sum_eq_canonical
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    ∑ camera ∈ canonicalFiniteCameraAtlas M,
      cameraResolvedIndependentReflectedHolomorphicDirectGreenPort
        M q hq0 hq1 S u v camera =
      canonicalC3IndependentReflectedHolomorphicDirectGreenPort M q hq0 hq1 S u v := by
  change
    ∑ camera ∈ canonicalFiniteCameraAtlas M,
      radialGreenDress (natDirichletTerm (operatorHeightParameter 0) 3)
        (cameraResolvedIndependentReflectedUndressedDirectGreenPort
          M q hq0 hq1 S u v camera) =
      radialGreenDress (natDirichletTerm (operatorHeightParameter 0) 3)
        (canonicalC3IndependentReflectedUndressedDirectGreenPort
          M q hq0 hq1 S u v)
  rw [← radialGreenDress_finset_sum,
    cameraResolvedIndependentReflectedUndressedDirectGreenPort_sum_eq_canonical]

/-- The fixed camera atlas synthesizes exactly to the canonical holomorphic
reflected port. -/
theorem cameraResolvedIndependentReflectedHolomorphicReflectedGreenPort_sum_eq_canonical
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    ∑ camera ∈ canonicalFiniteCameraAtlas M,
      cameraResolvedIndependentReflectedHolomorphicReflectedGreenPort
        M q hq0 hq1 S u v camera =
      canonicalC3IndependentReflectedHolomorphicReflectedGreenPort M q hq0 hq1 S u v := by
  change
    ∑ camera ∈ canonicalFiniteCameraAtlas M,
      radialGreenDress (natDirichletTerm (operatorHeightParameter v) 3)
        (cameraResolvedIndependentReflectedUndressedReflectedGreenPort
          M q hq0 hq1 S u v camera) =
      radialGreenDress (natDirichletTerm (operatorHeightParameter v) 3)
        (canonicalC3IndependentReflectedUndressedReflectedGreenPort
          M q hq0 hq1 S u v)
  rw [← radialGreenDress_finset_sum,
    cameraResolvedIndependentReflectedUndressedReflectedGreenPort_sum_eq_canonical]

/-- The sewn holomorphic Green scalar is defined at the canonical-port
level.  It is distinct from the radial/reflected historical four-corner
component unless a further crosswalk is supplied. -/
def canonicalC3IndependentReflectedHolomorphicGreenBoundary
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) : ℂ :=
  greenForm (𝕜 := ℂ)
    (canonicalC3IndependentReflectedHolomorphicDirectGreenPort M q hq0 hq1 S u v)
    (canonicalC3IndependentReflectedHolomorphicReflectedGreenPort M q hq0 hq1 S u v)

/-- Sewing the finite camera-pair atlas is exactly the canonical holomorphic
Green form.  This theorem is purely finite algebra and does not identify the
result with the historical radial/reflected four-corner component. -/
theorem canonicalC3IndependentReflectedHolomorphicGreenBoundary_eq_cameraPairwise
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    canonicalC3IndependentReflectedHolomorphicGreenBoundary M q hq0 hq1 S u v =
      ∑ directCamera ∈ canonicalFiniteCameraAtlas M,
        ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
          canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel
            M q hq0 hq1 S u v directCamera reflectedCamera := by
  unfold canonicalC3IndependentReflectedHolomorphicGreenBoundary
    canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel
  rw [← cameraResolvedIndependentReflectedHolomorphicDirectGreenPort_sum_eq_canonical,
    ← cameraResolvedIndependentReflectedHolomorphicReflectedGreenPort_sum_eq_canonical]
  exact greenForm_finset_sum_pairwise
    (canonicalFiniteCameraAtlas M) (canonicalFiniteCameraAtlas M)
    (cameraResolvedIndependentReflectedHolomorphicDirectGreenPort M q hq0 hq1 S u v)
    (cameraResolvedIndependentReflectedHolomorphicReflectedGreenPort M q hq0 hq1 S u v)

/-- Exact Green-form provenance for the historical four-corner component.
The factor is the historical radial coefficient, not the holomorphic
eigenvalue-collision factor used by the independent-reflected kernel. -/
theorem canonicalCompletedNativeHistoricalFourCornerGreenComponent_eq
    (M : ℕ) (z w : ℂ) :
    canonicalCompletedNativeHistoricalFourCornerGreenComponent M z w =
      canonicalC3MixedRadialCoefficient z w *
        nativeGpreFourCornerPolarizedDirichletPrefix
          M w (reflectedParameter z) := by
  simpa [canonicalCompletedNativeHistoricalFourCornerGreenComponent] using
    (canonicalCompletedNativeCarryGreenFourCornerProvenance M z w).1

/-- The pre-Hankel four-corner prefix is the literal Hilbert pairing of the
ordinary prefix and the reflected prefix. -/
theorem canonicalCompletedNativeHistoricalFourCornerPrefix_eq_inner
    (M : ℕ) (z w : ℂ) :
    nativeGpreFourCornerPolarizedDirichletPrefix
        M w (reflectedParameter z) =
      inner ℂ
        (canonicalCompletedC3DirichletGradientPrefixState w M)
        (canonicalCompletedC3DirichletGradientPrefixState
          (reflectedParameter z) M) := by
  exact (canonicalCompletedNativeCarryGreenFourCornerProvenance M z w).2.1

/-- The reflected prefix in the historical four-corner cell is reconstructed
from the ordinary and logarithmic Dirichlet data.  This is the exact
ordinary/log-jet statement available downstream; it is not a claim about the
derivative of the new independent-reflected holomorphic source. -/
theorem canonicalCompletedNativeHistoricalFourCornerPrefix_eq_logJetReconstruction
    (M : ℕ) (z w : ℂ) :
    nativeGpreFourCornerPolarizedDirichletPrefix
        M w (reflectedParameter z) =
      ∑ n ∈ Finset.range M,
        (starRingEnd ℂ) (positiveDirichletGradient w n) *
          sameEdgeRecoveredReflectedGradient n
            (positiveDirichletGradient z n)
            (positiveLogDirichletGradient z n) := by
  exact (canonicalCompletedNativeCarryGreenFourCornerProvenance M z w).2.2

/-! ## The completed scalar layer -/

/-- The completed fixed-center ledger has first variation exactly equal to
the canonical zeroth logarithmic moment.  Its definition retains all scalar
channels, so this theorem does not make the historical four-corner Green
component alone equal to `h₀`. -/
theorem canonicalCompletedNativeFixedCenterLedgerFirstVariation_eq_h0
    (M : ℕ) :
    deriv (canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator M) 0 =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) :=
  deriv_canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator_zero M

/-- The final real scalar readout is exactly the completed normalized
response divided-difference `dslope`, whenever its two characteristic
denominators are nonzero. -/
theorem canonicalCompletedNativeFinalRealReadout_eq_dslope
    (M : ℕ) (x z : ℝ)
    (hxF : completedNativeOperatorCharacteristic (x : ℂ) ≠ 0)
    (hzF : completedNativeOperatorCharacteristic (z : ℂ) ≠ 0) :
    canonicalCompletedC3AllCutoffRealKernelReadout M x z =
      dslope
        (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion) (x : ℂ) (z : ℂ) :=
  canonicalCompletedC3AllCutoffRealKernelReadout_eq_dslope M x z hxF hzF

/-- The existing scalar readout has the canonical polarized moment limit at
every pair of forward-difference orders. -/
theorem canonicalCompletedNativeFinalRealReadout_forwardDifference_tendsto_moment
    (M p q : ℕ) :
    Tendsto
      (fun k ↦ completedGreenKernelForwardDifference
        (canonicalCompletedC3AllCutoffRealAxisKernelReadout M)
        (canonicalGreenJetStep k) p q)
      atTop
      (nhds (polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment p q)) :=
  canonicalCompletedC3AllCutoffRealAxisKernelForwardDifference_tendsto_moment M p q

/-! ## Explicit downstream gate -/

/-- If a jet carrier built from the holomorphic Green readout is proved to
realize the canonical Green--Wronskian moment kernel, then the already
formalized incidence transport supplies the exact finite native
Jacobi/height construction.  The premise `hbridge` is intentionally the one
unclosed Green-to-moment interface; no old enriched-Taylor carrier is used to
manufacture it. -/
theorem holomorphicGreenMomentInterface_implies_finiteHeightOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {base radius : ℕ} {holomorphicJet : (ℕ ⊕ ℕ) → E}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (hbridge : IsGreenWronskianMomentKernelGramRepresentation
      canonicalCompletedNativeLogDerivativeMoment holomorphicJet)
    (transport : BR2BracketIncidenceJetTransport base radius holomorphicJet)
    (N : ℕ) :
    ∃ hpos : CanonicalCompletedNativeStieltjesPositivity,
      nativeGeometryFiniteHeightOperator hpos N =
        canonicalFiniteHeightOperator
          (greenWronskianMomentKernel_odd_shiftedMomentGram hbridge)
          N
          (canonicalCompletedNativeStieltjes_hankelGram_posDef hpos N)
          (greenJetOdd_prefix_linearIndependent
            (transport.odd_linearIndependent hbase hradius) N) := by
  exact nativeGeometryFiniteHeightOperator_eq_of_greenMomentKernel_and_incidenceTransport
    hbase hradius hbridge transport N

/-- The same explicit moment-interface gate yields the established native
camera-to-Jacobi-to-height provenance chain. -/
theorem holomorphicGreenMomentInterface_implies_nativeGeometryChain
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {base radius : ℕ} {holomorphicJet : (ℕ ⊕ ℕ) → E}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (hbridge : IsGreenWronskianMomentKernelGramRepresentation
      canonicalCompletedNativeLogDerivativeMoment holomorphicJet)
    (transport : BR2BracketIncidenceJetTransport base radius holomorphicJet)
    (cutoff N : ℕ) :
    ∃ hpos : CanonicalCompletedNativeStieltjesPositivity,
      normalizedCompletedNativeCameraCharacteristic 3 cutoff =
          (fun time : ℝ ↦ completedNativeOperatorCharacteristic (time : ℂ)) ∧
        completedNativeCameraLogDerivativeMoment 3 cutoff =
          canonicalCompletedNativeLogDerivativeMoment ∧
        (∃ hgram :
            (hankelGram
              (completedNativeCameraLogDerivativeMoment 3 cutoff) N).PosDef,
          canonicalFiniteJacobiSection
              (completedNativeCameraLogDerivativeMoment 3 cutoff) N hgram =
            canonicalCompletedNativeStieltjesFiniteJacobiTower hpos N) ∧
        (nativeGeometryFiniteHeightOperator hpos N).IsSymm := by
  exact nativeGeometry_to_finiteHeight_chain_of_greenMomentKernel_and_incidenceTransport
    hbase hradius hbridge transport cutoff N

end

end CarrySelfAdjointOperator
