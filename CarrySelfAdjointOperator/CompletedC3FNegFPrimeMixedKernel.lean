import CarrySelfAdjointOperator.CompletedC3MixedGreenWronskianDefect
import Mathlib.Tactic

/-!
# Mixed completed `(F, -F')` C3 kernel

The raw C3 mixed ledger lives in the spectral parameter `s`, while the
completed characteristic lives in the centered height parameter `z` with
`s = 1/2 + i z`.  This file retains that coordinate rotation explicitly,
then applies the exact product rule for the xi completion and the C3 chart
normalization.

No channel is projected away.  The final finite carrier retains:

* the mixed radial Green channel;
* block Green provenance;
* ordered cross-coordinate provenance;
* the height-coordinate readout residual;
* the explicit head--tail correction;
* the archimedean/chart product channel.
-/

open scoped BigOperators ComplexConjugate Topology

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary
open Filter

noncomputable section

/-! ## Completed scalar specialization -/

/-- The independently completed enriched TFVD trace pair specializes to the
actual completed characteristic and its canonical companion at two
independent points. -/
theorem mixedScalarBoundaryWedge_completedTrace_eq_F_negFprime
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    mixedScalarBoundaryWedge
        (canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout z)
        (canonicalCompletedC3EnrichedTfvdBoundaryCompanion z)
        (canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout w)
        (canonicalCompletedC3EnrichedTfvdBoundaryCompanion w) =
      completedGreenWronskian
        completedNativeOperatorCharacteristic
        (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
        z w := by
  rw [canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout_eq_characteristic
      hz,
    canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout_eq_characteristic
      hw,
    canonicalCompletedC3EnrichedTfvdBoundaryCompanion_eq_completedNativeOperatorBoundaryCompanion
      hz,
    canonicalCompletedC3EnrichedTfvdBoundaryCompanion_eq_completedNativeOperatorBoundaryCompanion
      hw]
  rfl

/-! ## Raw C3 trace in the centered height coordinate -/

/-- Tail-completed raw C3 chart pulled back to the height coordinate. -/
def canonicalCompletedC3RawHeightValue (z : ℂ) : ℂ :=
  canonicalCompletedC3EnrichedTfvdValueTailReadout
    (operatorHeightParameter z)

/-- The raw log jet acquires the chain-rule factor `i` in the height
coordinate. -/
def canonicalCompletedC3RawHeightCompanion (z : ℂ) : ℂ :=
  Complex.I * canonicalCompletedC3EnrichedTfvdLogJetTailReadout
    (operatorHeightParameter z)

/-- Mixed Wronskian of the raw chart after the exact height-coordinate
rotation. -/
def canonicalCompletedC3RawHeightMixedWronskian (z w : ℂ) : ℂ :=
  completedGreenWronskian
    canonicalCompletedC3RawHeightValue
    canonicalCompletedC3RawHeightCompanion z w

/-! ## Canonical chart factor in height coordinates -/

def canonicalC3ChartFactorHeight (z : ℂ) : ℂ :=
  cpChartFactor 3 (operatorHeightParameter z)

/-- Independent chain-rule companion of the C3 chart factor. -/
def canonicalC3ChartFactorHeightCompanion (z : ℂ) : ℂ :=
  -Complex.I * deriv (cpChartFactor 3) (operatorHeightParameter z)

theorem canonicalC3ChartFactorHeight_ne_zero
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalC3ChartFactorHeight z ≠ 0 := by
  unfold canonicalC3ChartFactorHeight
  exact cpChartFactor_ne_zero_on_genuineCriticalStrip 3 (by norm_num) hs

/-! ## Raw chart = chart factor times normalized native trace -/

theorem canonicalCompletedC3RawHeightValue_eq_chart_mul_normalized
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3RawHeightValue z =
      canonicalC3ChartFactorHeight z *
        canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout z := by
  have hfactor := canonicalC3ChartFactorHeight_ne_zero hs
  have hfactor' :
      cpChartFactor 3 (operatorHeightParameter z) ≠ 0 := by
    simpa [canonicalC3ChartFactorHeight] using hfactor
  unfold canonicalCompletedC3RawHeightValue
    canonicalC3ChartFactorHeight
    canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout
  exact (mul_div_cancel₀
    (canonicalCompletedC3EnrichedTfvdValueTailReadout
      (operatorHeightParameter z)) hfactor').symm

theorem canonicalCompletedC3RawHeightCompanion_eq_chartProductCompanion
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3RawHeightCompanion z =
      productBoundaryCompanion
        canonicalC3ChartFactorHeight
        canonicalC3ChartFactorHeightCompanion
        canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout
        canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout z := by
  have hfactor := canonicalC3ChartFactorHeight_ne_zero hs
  have hfactor' :
      cpChartFactor 3 (operatorHeightParameter z) ≠ 0 := by
    simpa [canonicalC3ChartFactorHeight] using hfactor
  unfold canonicalCompletedC3RawHeightCompanion
    canonicalC3ChartFactorHeight
    canonicalC3ChartFactorHeightCompanion
    canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout
    canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout
    productBoundaryCompanion
  dsimp only
  field_simp [hfactor']
  ring

/-- The raw height Wronskian is exactly the product-rule Wronskian of the
chart factor and normalized native trace. -/
theorem canonicalCompletedC3RawHeightMixedWronskian_eq_chartProduct
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3RawHeightMixedWronskian z w =
      completedGreenWronskian
        (fun u : ℂ => canonicalC3ChartFactorHeight u *
          canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout u)
        (productBoundaryCompanion
          canonicalC3ChartFactorHeight
          canonicalC3ChartFactorHeightCompanion
          canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout
          canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout)
        z w := by
  unfold canonicalCompletedC3RawHeightMixedWronskian
    completedGreenWronskian
  rw [canonicalCompletedC3RawHeightValue_eq_chart_mul_normalized hz,
    canonicalCompletedC3RawHeightValue_eq_chart_mul_normalized hw,
    canonicalCompletedC3RawHeightCompanion_eq_chartProductCompanion hz,
    canonicalCompletedC3RawHeightCompanion_eq_chartProductCompanion hw]

/-! ## Division-free crossed product identity -/

/-- Hermitian two-point weight attached to one scalar channel. -/
def mixedHermitianWeight (H : ℂ → ℂ) (z w : ℂ) : ℂ :=
  H z * (starRingEnd ℂ) (H w)

/-- The completion/chart correction that remains separate from the raw C3
ledger.  It contains the xi-factor and chart-factor Wronskians before any
real-part projection. -/
def canonicalCompletedC3ArchimedeanChartMixedChannel (z w : ℂ) : ℂ :=
  mixedHermitianWeight
      canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout z w *
    (mixedHermitianWeight canonicalC3ChartFactorHeight z w *
        completedGreenWronskian
          nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion z w -
      mixedHermitianWeight nativeXiCompletionFactor z w *
        completedGreenWronskian
          canonicalC3ChartFactorHeight
          canonicalC3ChartFactorHeightCompanion z w)

/-- Cross-multiplication of the two exact product rules.  The normalized
Wronskian is retained during the proof and cancels only algebraically between
the two complete product identities. -/
theorem canonicalCompletedC3Trace_crossedChartIdentity
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    mixedHermitianWeight canonicalC3ChartFactorHeight z w *
        completedGreenWronskian
          canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
          canonicalCompletedC3EnrichedTfvdBoundaryCompanion z w =
      mixedHermitianWeight nativeXiCompletionFactor z w *
          canonicalCompletedC3RawHeightMixedWronskian z w +
        canonicalCompletedC3ArchimedeanChartMixedChannel z w := by
  rw [canonicalCompletedC3RawHeightMixedWronskian_eq_chartProduct hz hw]
  unfold canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
    canonicalCompletedC3EnrichedTfvdBoundaryCompanion
  rw [completedGreenWronskian_mul, completedGreenWronskian_mul]
  unfold canonicalCompletedC3ArchimedeanChartMixedChannel
    mixedHermitianWeight
  ring

/-- The crossed identity specialized to the actual completed pair `(F,-F')`.
No diagonal specialization, zero hypothesis, or scalar projection occurs. -/
theorem completedFNegFPrimeWronskian_crossedChartIdentity
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    mixedHermitianWeight canonicalC3ChartFactorHeight z w *
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
          z w =
      mixedHermitianWeight nativeXiCompletionFactor z w *
          canonicalCompletedC3RawHeightMixedWronskian z w +
        canonicalCompletedC3ArchimedeanChartMixedChannel z w := by
  rw [← mixedScalarBoundaryWedge_completedTrace_eq_F_negFprime hz hw,
    mixedScalarBoundaryWedge_eq_completedGreenWronskian]
  exact canonicalCompletedC3Trace_crossedChartIdentity hz hw

/-! ## Height-rotated finite mixed ledger -/

/-- Four synthesis residuals after the chain-rule rotation of each log-jet
by `i`.  The local C3 legs themselves are unchanged. -/
def canonicalMixedBoundaryHeightReadoutResidualCorrection
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (z w : ℂ) : ℂ :=
  let dataZ := canonicalBoundaryResidualData M kappa omega z
  let dataW := canonicalBoundaryResidualData M kappa omega w
  let legs := canonicalMixedBoundaryResidualLegs M kappa omega z w
  mixedBoundaryResidualCorrection
    dataZ.valueReadout (Complex.I * dataZ.logJetReadout)
    dataW.valueReadout (Complex.I * dataW.logJetReadout) legs

/-- Three finite structural channels with the height-coordinate residual kept
independent of Green and ordered cross provenance. -/
def canonicalMixedBoundaryHeightStructuralDefect
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (z w : ℂ) : ℂ :=
  canonicalMixedBoundaryGreenProvenance M kappa omega z w +
    canonicalMixedBoundaryCrossProvenance M kappa omega z w +
    canonicalMixedBoundaryHeightReadoutResidualCorrection
      M kappa omega z w

/-- Exact finite Green decomposition after rotating the two log-jet targets
to height companions.  No local leg or provenance channel is changed. -/
theorem canonicalMixedEnrichedHeightScalarBoundary_eq_green_add_explicitDefects
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (z w : ℂ) :
    mixedScalarBoundaryWedge
        (canonicalBoundaryResidualData M kappa omega z).valueReadout
        (Complex.I *
          (canonicalBoundaryResidualData M kappa omega z).logJetReadout)
        (canonicalBoundaryResidualData M kappa omega w).valueReadout
        (Complex.I *
          (canonicalBoundaryResidualData M kappa omega w).logJetReadout) =
      greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair (3 * M) w)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (reflectedParameter z)) +
        canonicalMixedBoundaryHeightStructuralDefect
          M kappa omega z w := by
  let pair := canonicalMixedBoundaryResidualPair kappa omega z w
  let direct := finiteC3EnrichedTfvdPairTransport M kappa omega w pair
  let reflectedPair := canonicalBoundaryResidualPair
    kappa omega (reflectedParameter z)
  let reflected := finiteC3EnrichedTfvdPairTransport
    M kappa omega (reflectedParameter z) reflectedPair
  let legs := canonicalMixedBoundaryResidualLegs M kappa omega z w
  have hlocal :
      (∑ mr : Fin M × Fin 2,
        sameSEdgeBoundaryWedge
          (legs.left mr) (legs.right mr)
          (legs.jetLeft mr) (legs.jetRight mr)) =
        finiteC3EnrichedTfvdPairBoundaryForm M direct := by
    simpa [pair, direct, legs, canonicalMixedBoundaryResidualPair,
      canonicalMixedBoundaryResidualLegs] using
      (sum_enrichedTfvdBoundaryEdges_eq_pairBoundaryForm
        M kappa omega w pair)
  have htrace :=
    mixedScalarBoundaryWedge_eq_localTwoLeg_add_cross_add_residualCorrection
      (canonicalBoundaryResidualData M kappa omega z).valueReadout
      (Complex.I *
        (canonicalBoundaryResidualData M kappa omega z).logJetReadout)
      (canonicalBoundaryResidualData M kappa omega w).valueReadout
      (Complex.I *
        (canonicalBoundaryResidualData M kappa omega w).logJetReadout)
      legs
  rw [hlocal] at htrace
  have hgreen :=
    finiteC3EnrichedTfvdPairBoundary_eq_greenForm_add_provenance_twoParameter
      M kappa omega w (reflectedParameter z) pair reflectedPair
  dsimp only at hgreen
  change finiteC3EnrichedTfvdPairBoundaryForm M direct =
      greenForm direct.greenPort reflected.greenPort +
        finiteC3EnrichedTfvdPairGreenProvenance
          M kappa omega pair direct reflected at hgreen
  have hdirectPort :
      direct.greenPort =
        finiteC3GenuineBracketGreenBoundaryPair (M * 3) w := by
    simpa [direct, pair, canonicalMixedBoundaryResidualPair,
      canonicalBoundaryResidualPair,
      canonicalEnrichedTfvdValueLogJetPair,
      finiteC3EnrichedTfvdPairTransport] using
      (finiteC3EnrichedTfvdValueGreenPort_canonical
        M hkappa omega homega w)
  have hreflectedPort :
      reflected.greenPort =
        finiteC3GenuineBracketGreenBoundaryPair
          (M * 3) (reflectedParameter z) := by
    simpa [reflected, reflectedPair, canonicalBoundaryResidualPair,
      canonicalEnrichedTfvdValueLogJetPair,
      finiteC3EnrichedTfvdPairTransport] using
      (finiteC3EnrichedTfvdValueGreenPort_canonical
        M hkappa omega homega (reflectedParameter z))
  rw [htrace, hgreen, hdirectPort, hreflectedPort]
  unfold canonicalMixedBoundaryHeightStructuralDefect
    canonicalMixedBoundaryGreenProvenance
    canonicalMixedBoundaryCrossProvenance
    canonicalMixedBoundaryHeightReadoutResidualCorrection
  dsimp only [pair, direct, reflectedPair, reflected, legs]
  rw [Nat.mul_comm M 3]
  ring

/-- Canonical C3 specialization of the three height-rotated finite defect
channels. -/
def canonicalC3FiniteMixedHeightStructuralDefect
    (M : ℕ) (z w : ℂ) : ℂ :=
  canonicalMixedBoundaryHeightStructuralDefect
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) z w

/-- The finite raw head, pulled back to the centered height coordinate. -/
def canonicalC3FiniteMixedHeightHeadWronskian
    (M : ℕ) (z w : ℂ) : ℂ :=
  mixedScalarBoundaryWedge
    (finiteBracketedDirichletChart 3 M (operatorHeightParameter z))
    (Complex.I *
      finiteCanonicalLogBracketChart M (operatorHeightParameter z))
    (finiteBracketedDirichletChart 3 M (operatorHeightParameter w))
    (Complex.I *
      finiteCanonicalLogBracketChart M (operatorHeightParameter w))

/-- The height-rotated finite head is Green plus the three explicit finite
structural channels. -/
theorem canonicalC3FiniteMixedHeightHeadWronskian_eq_green_add_structuralDefect
    (M : ℕ) (z w : ℂ) :
    canonicalC3FiniteMixedHeightHeadWronskian M z w =
      greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (operatorHeightParameter w))
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M)
              (reflectedParameter (operatorHeightParameter z))) +
        canonicalC3FiniteMixedHeightStructuralDefect M
          (operatorHeightParameter z) (operatorHeightParameter w) := by
  have hmixed :=
    canonicalMixedEnrichedHeightScalarBoundary_eq_green_add_explicitDefects
      M tfvdHaarScale_ne_zero (fun _ : ℕ => (1 : ℂ))
      (by intro m; norm_num)
      (operatorHeightParameter z) (operatorHeightParameter w)
  have hzTransport := finiteC3EnrichedTfvdPairTransport_canonical
    M tfvdHaarScale_ne_zero (fun _ : ℕ => (1 : ℂ))
      (by intro m; norm_num) (operatorHeightParameter z)
  have hwTransport := finiteC3EnrichedTfvdPairTransport_canonical
    M tfvdHaarScale_ne_zero (fun _ : ℕ => (1 : ℂ))
      (by intro m; norm_num) (operatorHeightParameter w)
  dsimp only at hzTransport hwTransport
  have hzValue :
      (canonicalBoundaryResidualData M tfvdHaarScale
        (fun _ : ℕ => (1 : ℂ))
        (operatorHeightParameter z)).valueReadout =
          finiteBracketedDirichletChart 3 M
            (operatorHeightParameter z) := by
    simpa [canonicalBoundaryResidualData, canonicalBoundaryResidualPair]
      using hzTransport.1
  have hzLog :
      (canonicalBoundaryResidualData M tfvdHaarScale
        (fun _ : ℕ => (1 : ℂ))
        (operatorHeightParameter z)).logJetReadout =
          finiteCanonicalLogBracketChart M
            (operatorHeightParameter z) := by
    simpa [canonicalBoundaryResidualData, canonicalBoundaryResidualPair]
      using hzTransport.2.1
  have hwValue :
      (canonicalBoundaryResidualData M tfvdHaarScale
        (fun _ : ℕ => (1 : ℂ))
        (operatorHeightParameter w)).valueReadout =
          finiteBracketedDirichletChart 3 M
            (operatorHeightParameter w) := by
    simpa [canonicalBoundaryResidualData, canonicalBoundaryResidualPair]
      using hwTransport.1
  have hwLog :
      (canonicalBoundaryResidualData M tfvdHaarScale
        (fun _ : ℕ => (1 : ℂ))
        (operatorHeightParameter w)).logJetReadout =
          finiteCanonicalLogBracketChart M
            (operatorHeightParameter w) := by
    simpa [canonicalBoundaryResidualData, canonicalBoundaryResidualPair]
      using hwTransport.2.1
  rw [hzValue, hzLog, hwValue, hwLog] at hmixed
  simpa [canonicalC3FiniteMixedHeightHeadWronskian,
    canonicalC3FiniteMixedHeightStructuralDefect] using hmixed

/-! ## Height-rotated tail completion -/

/-- Head--tail correction after both companion channels acquire the exact
height-coordinate factor `i`. -/
def canonicalC3MixedHeightTailCompletionDefect
    (M : ℕ) (z w : ℂ) : ℂ :=
  mixedBoundaryCompletionCorrection
    (finiteBracketedDirichletChart 3 M (operatorHeightParameter z))
    (Complex.I *
      finiteCanonicalLogBracketChart M (operatorHeightParameter z))
    (finiteBracketedDirichletChart 3 M (operatorHeightParameter w))
    (Complex.I *
      finiteCanonicalLogBracketChart M (operatorHeightParameter w))
    (realCpBracketCutoffTail 3 M (operatorHeightParameter z))
    (Complex.I * canonicalC3LogJetCutoffTail M
      (operatorHeightParameter z))
    (realCpBracketCutoffTail 3 M (operatorHeightParameter w))
    (Complex.I * canonicalC3LogJetCutoffTail M
      (operatorHeightParameter w))

theorem canonicalCompletedC3RawHeightValue_eq_bracketedDirichletChart
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3RawHeightValue z =
      bracketedDirichletChart 3 (operatorHeightParameter z) := by
  have hsRe : -1 < (operatorHeightParameter z).re := by
    linarith [hs.1]
  unfold canonicalCompletedC3RawHeightValue
    canonicalCompletedC3EnrichedTfvdValueTailReadout
  exact NativeCarryC3Crosswalk.finiteC3CanonicalEnrichedTfvdPairTailReadout_eq_chart
    1 tfvdHaarScale_ne_zero (fun _ : ℕ => (1 : ℂ))
      (by intro m; norm_num) hsRe

theorem canonicalCompletedC3RawHeightCompanion_eq_head_add_tail
    (M : ℕ) {z : ℂ}
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3RawHeightCompanion z =
      Complex.I * finiteCanonicalLogBracketChart M
          (operatorHeightParameter z) +
        Complex.I * canonicalC3LogJetCutoffTail M
          (operatorHeightParameter z) := by
  have hsHalf : operatorHeightParameter z ∈ bracketHalfPlane := by
    change -1 < (operatorHeightParameter z).re
    linarith [hs.1]
  have hcompleted :=
    canonicalCompletedC3FiniteEnrichedTfvdLogJetTailReadout_eq_completed
      M hsHalf
  unfold canonicalCompletedC3RawHeightCompanion
  unfold canonicalCompletedC3FiniteEnrichedTfvdLogJetTailReadout at hcompleted
  rw [← hcompleted]
  ring

/-- The raw height Wronskian is exactly its finite head plus the independently
expanded height-rotated tail correction. -/
theorem canonicalCompletedC3RawHeightMixedWronskian_eq_head_add_tailDefect
    (M : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3RawHeightMixedWronskian z w =
      canonicalC3FiniteMixedHeightHeadWronskian M z w +
        canonicalC3MixedHeightTailCompletionDefect M z w := by
  have hzRe : -1 < (operatorHeightParameter z).re := by
    linarith [hz.1]
  have hwRe : -1 < (operatorHeightParameter w).re := by
    linarith [hw.1]
  unfold canonicalCompletedC3RawHeightMixedWronskian
    completedGreenWronskian
  rw [canonicalCompletedC3RawHeightValue_eq_bracketedDirichletChart hz,
    canonicalCompletedC3RawHeightValue_eq_bracketedDirichletChart hw,
    bracketedDirichletChart_eq_finite_add_cutoffTail
      3 M (by norm_num) hzRe,
    bracketedDirichletChart_eq_finite_add_cutoffTail
      3 M (by norm_num) hwRe,
    canonicalCompletedC3RawHeightCompanion_eq_head_add_tail M hz,
    canonicalCompletedC3RawHeightCompanion_eq_head_add_tail M hw]
  exact mixedScalarBoundaryWedge_add_tails _ _ _ _ _ _ _ _

/-- Convergence of the finite log-jet head to the completed log-jet. -/
theorem finiteCanonicalLogBracketChart_tendsto_completed
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun M : ℕ => finiteCanonicalLogBracketChart M s)
      atTop
      (nhds (canonicalCompletedC3EnrichedTfvdLogJetTailReadout s)) := by
  have htail := canonicalC3LogJetCutoffTail_tendsto_zero hs
  have hconstant : Tendsto
      (fun _ : ℕ =>
        canonicalCompletedC3EnrichedTfvdLogJetTailReadout s)
      atTop
      (nhds (canonicalCompletedC3EnrichedTfvdLogJetTailReadout s)) :=
    tendsto_const_nhds
  have hsub : Tendsto
      (fun M : ℕ =>
        canonicalCompletedC3EnrichedTfvdLogJetTailReadout s -
          canonicalC3LogJetCutoffTail M s)
      atTop
      (nhds (canonicalCompletedC3EnrichedTfvdLogJetTailReadout s)) := by
    simpa using hconstant.sub htail
  refine hsub.congr' (Eventually.of_forall fun M => ?_)
  have hfull :=
    canonicalCompletedC3FiniteEnrichedTfvdLogJetTailReadout_eq_completed
      M (s := s) (by change -1 < s.re; linarith)
  change canonicalCompletedC3EnrichedTfvdLogJetTailReadout s -
      canonicalC3LogJetCutoffTail M s =
    finiteCanonicalLogBracketChart M s
  unfold canonicalCompletedC3FiniteEnrichedTfvdLogJetTailReadout at hfull
  exact (eq_sub_of_add_eq hfull).symm

/-- The height-rotated head--tail correction vanishes on the product strip.
This uses only convergence of the four heads and four tails. -/
theorem canonicalC3MixedHeightTailCompletionDefect_tendsto_zero
    {z w : ℂ}
    (hz : 0 < (operatorHeightParameter z).re)
    (hw : 0 < (operatorHeightParameter w).re) :
    Tendsto
      (fun M : ℕ => canonicalC3MixedHeightTailCompletionDefect M z w)
      atTop (nhds 0) := by
  let sZ := operatorHeightParameter z
  let sW := operatorHeightParameter w
  have hzValue := finiteBracketedDirichletChart_tendsto
    3 (by norm_num) (s := sZ) (by dsimp [sZ]; linarith)
  have hwValue := finiteBracketedDirichletChart_tendsto
    3 (by norm_num) (s := sW) (by dsimp [sW]; linarith)
  have hzValueTail := realCpBracketCutoffTail_tendsto_zero
    3 (by norm_num) (s := sZ) (by dsimp [sZ]; linarith)
  have hwValueTail := realCpBracketCutoffTail_tendsto_zero
    3 (by norm_num) (s := sW) (by dsimp [sW]; linarith)
  have hzCompanion :=
    (finiteCanonicalLogBracketChart_tendsto_completed
      (s := sZ) (by dsimp [sZ]; linarith)).const_mul Complex.I
  have hwCompanion :=
    (finiteCanonicalLogBracketChart_tendsto_completed
      (s := sW) (by dsimp [sW]; linarith)).const_mul Complex.I
  have hzCompanionTail :=
    (canonicalC3LogJetCutoffTail_tendsto_zero
      (s := sZ) (by dsimp [sZ]; linarith)).const_mul Complex.I
  have hwCompanionTail :=
    (canonicalC3LogJetCutoffTail_tendsto_zero
      (s := sW) (by dsimp [sW]; linarith)).const_mul Complex.I
  unfold canonicalC3MixedHeightTailCompletionDefect
    mixedBoundaryCompletionCorrection
  have h1 := hzCompanion.mul hwValueTail.star
  have h2 := hzCompanionTail.mul hwValue.star
  have h3 := hzCompanionTail.mul hwValueTail.star
  have h4 := hzValue.mul hwCompanionTail.star
  have h5 := hzValueTail.mul hwCompanion.star
  have h6 := hzValueTail.mul hwCompanionTail.star
  simpa [sZ, sW] using (((h1.add h2).add h3).sub h4).sub h5 |>.sub h6

/-! ## Six-channel completed carrier -/

/-- Product carrier for every channel used by the final mixed readout. -/
structure CanonicalCompletedC3FNegFPrimeMixedChannels where
  radialGreen : ℂ
  greenProvenance : ℂ
  offDiagonal : ℂ
  readoutResidual : ℂ
  tailCompletion : ℂ
  archimedeanChart : ℂ

/-- The only operation that combines the six retained channels. -/
def CanonicalCompletedC3FNegFPrimeMixedChannels.finalReadout
    (channels : CanonicalCompletedC3FNegFPrimeMixedChannels) : ℂ :=
  channels.radialGreen + channels.greenProvenance +
    channels.offDiagonal + channels.readoutResidual +
    channels.tailCompletion + channels.archimedeanChart

/-- Finite six-channel ledger for the actual completed pair `(F,-F')`. -/
def canonicalCompletedC3FiniteFNegFPrimeMixedChannels
    (M : ℕ) (z w : ℂ) :
    CanonicalCompletedC3FNegFPrimeMixedChannels :=
  let sZ := operatorHeightParameter z
  let sW := operatorHeightParameter w
  let xiWeight := mixedHermitianWeight nativeXiCompletionFactor z w
  {
    radialGreen := xiWeight *
      greenForm (𝕜 := ℂ)
        (finiteC3GenuineBracketGreenBoundaryPair (3 * M) sW)
        (finiteC3GenuineBracketGreenBoundaryPair
          (3 * M) (reflectedParameter sZ))
    greenProvenance := xiWeight *
      canonicalMixedBoundaryGreenProvenance M tfvdHaarScale
        (fun _ : ℕ => (1 : ℂ)) sZ sW
    offDiagonal := xiWeight *
      canonicalMixedBoundaryCrossProvenance M tfvdHaarScale
        (fun _ : ℕ => (1 : ℂ)) sZ sW
    readoutResidual := xiWeight *
      canonicalMixedBoundaryHeightReadoutResidualCorrection
        M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) sZ sW
    tailCompletion := xiWeight *
      canonicalC3MixedHeightTailCompletionDefect M z w
    archimedeanChart :=
      canonicalCompletedC3ArchimedeanChartMixedChannel z w
  }

/-- Exact global finite Green--Wronskian sewing for `(F,-F')`, with all six
channels present in the conclusion. -/
theorem finalScalarReadout_eq_completedFNegFPrimeWronskian
    (M : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    (canonicalCompletedC3FiniteFNegFPrimeMixedChannels M z w).finalReadout =
      mixedHermitianWeight canonicalC3ChartFactorHeight z w *
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
          z w := by
  have hhead :=
    canonicalC3FiniteMixedHeightHeadWronskian_eq_green_add_structuralDefect
      M z w
  have htail :=
    canonicalCompletedC3RawHeightMixedWronskian_eq_head_add_tailDefect
      M hz hw
  have hcross := completedFNegFPrimeWronskian_crossedChartIdentity hz hw
  unfold canonicalC3FiniteMixedHeightStructuralDefect
    canonicalMixedBoundaryHeightStructuralDefect at hhead
  rw [hhead] at htail
  unfold canonicalCompletedC3FiniteFNegFPrimeMixedChannels
    CanonicalCompletedC3FNegFPrimeMixedChannels.finalReadout
  dsimp only
  rw [hcross, htail]
  ring

theorem canonicalC3ChartMixedHermitianWeight_ne_zero
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    mixedHermitianWeight canonicalC3ChartFactorHeight z w ≠ 0 := by
  unfold mixedHermitianWeight
  exact mul_ne_zero
    (canonicalC3ChartFactorHeight_ne_zero hz) (by
      simpa using canonicalC3ChartFactorHeight_ne_zero hw)

/-- Literal unscaled global Green--Wronskian identity.  Normalization by the
nonzero C3 chart weight is applied only after the six channels have reached
their final readout. -/
theorem finalScalarReadout_div_chartWeight_eq_completedFNegFPrimeWronskian
    (M : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    (canonicalCompletedC3FiniteFNegFPrimeMixedChannels M z w).finalReadout /
        mixedHermitianWeight canonicalC3ChartFactorHeight z w =
      completedGreenWronskian
        completedNativeOperatorCharacteristic
        (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
        z w := by
  apply (div_eq_iff (canonicalC3ChartMixedHermitianWeight_ne_zero hz hw)).2
  rw [finalScalarReadout_eq_completedFNegFPrimeWronskian M hz hw]
  ring

/-! ## Completion and the exact global frontier -/

/-- The full six-channel finite readout converges to the actual completed
Wronskian.  In fact it is already equal to that value at every cutoff. -/
theorem finalScalarReadout_tendsto_completedFNegFPrimeWronskian
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ =>
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels M z w).finalReadout)
      atTop
      (nhds
        (mixedHermitianWeight canonicalC3ChartFactorHeight z w *
          completedGreenWronskian
            completedNativeOperatorCharacteristic
            (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
            z w)) := by
  exact tendsto_const_nhds.congr'
    (Eventually.of_forall fun M =>
      (finalScalarReadout_eq_completedFNegFPrimeWronskian M hz hw).symm)

/-- Exact raw sewing before multiplication by the xi weight. -/
theorem canonicalCompletedC3RawHeightMixedWronskian_eq_green_add_channels
    (M : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3RawHeightMixedWronskian z w =
      greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (operatorHeightParameter w))
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M)
              (reflectedParameter (operatorHeightParameter z))) +
        canonicalC3FiniteMixedHeightStructuralDefect M
          (operatorHeightParameter z) (operatorHeightParameter w) +
        canonicalC3MixedHeightTailCompletionDefect M z w := by
  rw [canonicalCompletedC3RawHeightMixedWronskian_eq_head_add_tailDefect
      M hz hw,
    canonicalC3FiniteMixedHeightHeadWronskian_eq_green_add_structuralDefect]

/-- In completion, the retained structural triple has the forced limit
`raw Wronskian - radial Green`.  Its vanishing is not assumed. -/
theorem canonicalC3FiniteMixedHeightStructuralDefect_tendsto
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ =>
        canonicalC3FiniteMixedHeightStructuralDefect M
          (operatorHeightParameter z) (operatorHeightParameter w))
      atTop
      (nhds
        (canonicalCompletedC3RawHeightMixedWronskian z w -
          canonicalCompletedC3MixedRadialGreenKernel
            (operatorHeightParameter z) (operatorHeightParameter w)
            hw.1
            (by
              simpa [reflectedParameter] using sub_pos.mpr hz.2))) := by
  have hgreen := finiteC3MixedRadialGreen_tendsto_completed
    (z := operatorHeightParameter z)
    (w := operatorHeightParameter w)
    hw.1
    (by simpa [reflectedParameter] using sub_pos.mpr hz.2)
  have htail := canonicalC3MixedHeightTailCompletionDefect_tendsto_zero
    hz.1 hw.1
  have hconstant : Tendsto
      (fun _ : ℕ => canonicalCompletedC3RawHeightMixedWronskian z w)
      atTop (nhds (canonicalCompletedC3RawHeightMixedWronskian z w)) :=
    tendsto_const_nhds
  have hlimit : Tendsto
      (fun M : ℕ =>
        canonicalCompletedC3RawHeightMixedWronskian z w -
          greenForm (𝕜 := ℂ)
            (finiteC3GenuineBracketGreenBoundaryPair
              (3 * M) (operatorHeightParameter w))
            (finiteC3GenuineBracketGreenBoundaryPair
              (3 * M)
                (reflectedParameter (operatorHeightParameter z))) -
          canonicalC3MixedHeightTailCompletionDefect M z w)
      atTop
      (nhds
        (canonicalCompletedC3RawHeightMixedWronskian z w -
          canonicalCompletedC3MixedRadialGreenKernel
            (operatorHeightParameter z) (operatorHeightParameter w)
            hw.1
            (by simpa [reflectedParameter] using sub_pos.mpr hz.2))) := by
    simpa using (hconstant.sub hgreen).sub htail
  refine hlimit.congr' (Eventually.of_forall fun M => ?_)
  have hsewing := canonicalCompletedC3RawHeightMixedWronskian_eq_green_add_channels
    M hz hw
  linear_combination hsewing

/-- The retained provenance, off-diagonal, and residual channels vanish in
completion exactly when the completed raw Wronskian is the completed radial
Green kernel.  This is a consequence of uniqueness of limits, not an extra
normalization convention. -/
theorem canonicalC3FiniteMixedHeightStructuralDefect_tendsto_zero_iff
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ =>
        canonicalC3FiniteMixedHeightStructuralDefect M
          (operatorHeightParameter z) (operatorHeightParameter w))
      atTop (nhds 0) ↔
    canonicalCompletedC3RawHeightMixedWronskian z w =
      canonicalCompletedC3MixedRadialGreenKernel
        (operatorHeightParameter z) (operatorHeightParameter w)
        hw.1
        (by
          simpa [reflectedParameter] using sub_pos.mpr hz.2) := by
  have hlimit := canonicalC3FiniteMixedHeightStructuralDefect_tendsto hz hw
  constructor
  · intro hzero
    exact sub_eq_zero.mp (tendsto_nhds_unique hlimit hzero)
  · intro hkernel
    rw [hkernel] at hlimit
    simpa using hlimit

/-- On the diagonal, the mixed radial coefficient is exactly the ordinary
C3 radial difference. -/
theorem canonicalC3MixedRadialCoefficient_self_eq_radialDifference
    (s : ℂ) :
    canonicalC3MixedRadialCoefficient s s =
      ((cpRadialDifference 3 (criticalDisplacement s.re) : ℝ) : ℂ) := by
  unfold canonicalC3MixedRadialCoefficient cpRadialDifference
  simp [reflectedParameter, criticalDisplacement]
  congr 1
  ring

/-- The completed diagonal radial Green kernel vanishes precisely on the
critical line.  The completed Gram factor is nonzero throughout the open
strip, so all vanishing is carried by the radial coefficient. -/
theorem canonicalCompletedC3MixedRadialGreenKernel_self_eq_zero_iff
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    canonicalCompletedC3MixedRadialGreenKernel s s hs.1
        (by
          simpa [reflectedParameter] using sub_pos.mpr hs.2) = 0 ↔
      s.re = (1 : ℝ) / 2 := by
  unfold canonicalCompletedC3MixedRadialGreenKernel
  rw [canonicalC3MixedRadialCoefficient_self_eq_radialDifference]
  have hgram :
      canonicalCompletedC3RawGammaGram s (reflectedParameter s) hs.1
          (by
            simpa [reflectedParameter] using sub_pos.mpr hs.2) ≠ 0 := by
    rw [canonicalCompletedC3RawGammaGram_reflected_eq_infinitePairing hs]
    exact infiniteReflectedGradientPairing_ne_zero hs
  constructor
  · intro hzero
    have hradialComplex :
        ((cpRadialDifference 3 (criticalDisplacement s.re) : ℝ) : ℂ) = 0 :=
      (mul_eq_zero.mp hzero).resolve_right hgram
    have hradial :
        cpRadialDifference 3 (criticalDisplacement s.re) = 0 := by
      exact_mod_cast hradialComplex
    have hcritical : criticalDisplacement s.re = 0 :=
      (cpRadialDifference_eq_zero_iff
        3 (by norm_num) (criticalDisplacement s.re)).1 hradial
    unfold criticalDisplacement at hcritical
    linarith
  · intro hre
    have hcritical : criticalDisplacement s.re = 0 := by
      unfold criticalDisplacement
      linarith
    rw [hcritical]
    simp [cpRadialDifference]

/-- A Genuine zero annihilates the completed raw value channel in the exact
centered-height coordinate. -/
theorem canonicalCompletedC3RawHeightValue_eq_zero_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    canonicalCompletedC3RawHeightValue (centeredHeightParameter s) = 0 := by
  have hheightStrip :
      operatorHeightParameter (centeredHeightParameter s) ∈
        genuineCriticalStrip := by
    simpa using hs
  rw [canonicalCompletedC3RawHeightValue_eq_bracketedDirichletChart
      hheightStrip,
    operatorHeightParameter_centeredHeightParameter]
  exact
    (bracketedDirichletChart_zero_iff_genuineContinuation_zero
      3 (by norm_num) (by norm_num) hs).2 hzero

/-- At a Genuine zero, the diagonal raw height Wronskian vanishes before
any radial or scalar identification is made. -/
theorem canonicalCompletedC3RawHeightMixedWronskian_self_eq_zero_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    canonicalCompletedC3RawHeightMixedWronskian
        (centeredHeightParameter s) (centeredHeightParameter s) = 0 := by
  unfold canonicalCompletedC3RawHeightMixedWronskian
    completedGreenWronskian
  rw [canonicalCompletedC3RawHeightValue_eq_zero_of_genuine_zero hs hzero]
  simp

/-- At a Genuine zero, the exact limit of the retained structural triple is
the negative completed radial Green kernel.  Thus the triple cancels the
radial channel unless the radial coefficient itself vanishes. -/
theorem canonicalC3FiniteMixedHeightStructuralDefect_tendsto_neg_radial_at_genuineZero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun M : ℕ => canonicalC3FiniteMixedHeightStructuralDefect M s s)
      atTop
      (nhds
        (-canonicalCompletedC3MixedRadialGreenKernel s s hs.1
          (by
            simpa [reflectedParameter] using sub_pos.mpr hs.2))) := by
  have hheightStrip :
      operatorHeightParameter (centeredHeightParameter s) ∈
        genuineCriticalStrip := by
    simpa using hs
  have hlimit := canonicalC3FiniteMixedHeightStructuralDefect_tendsto
    (z := centeredHeightParameter s) (w := centeredHeightParameter s)
    hheightStrip hheightStrip
  rw [canonicalCompletedC3RawHeightMixedWronskian_self_eq_zero_of_genuine_zero
      hs hzero] at hlimit
  simpa using hlimit

/-- At a Genuine zero, asking the provenance, off-diagonal, and residual
triple to disappear is equivalent to critical-line confinement itself.  In
particular, this vanishing cannot be imported as a consequence of completion
without proving the missing Green--Wronskian identification. -/
theorem canonicalC3FiniteMixedHeightStructuralDefect_tendsto_zero_at_genuineZero_iff
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun M : ℕ => canonicalC3FiniteMixedHeightStructuralDefect M s s)
      atTop (nhds 0) ↔
    s.re = (1 : ℝ) / 2 := by
  have hheightStrip :
      operatorHeightParameter (centeredHeightParameter s) ∈
        genuineCriticalStrip := by
    simpa using hs
  have hfrontier :=
    canonicalC3FiniteMixedHeightStructuralDefect_tendsto_zero_iff
      (z := centeredHeightParameter s) (w := centeredHeightParameter s)
      hheightStrip hheightStrip
  have hfrontier' :
      Tendsto
          (fun M : ℕ => canonicalC3FiniteMixedHeightStructuralDefect M s s)
          atTop (nhds 0) ↔
        canonicalCompletedC3RawHeightMixedWronskian
            (centeredHeightParameter s) (centeredHeightParameter s) =
          canonicalCompletedC3MixedRadialGreenKernel s s hs.1
            (by
              simpa [reflectedParameter] using sub_pos.mpr hs.2) := by
    simpa using hfrontier
  have hrawZero :=
    canonicalCompletedC3RawHeightMixedWronskian_self_eq_zero_of_genuine_zero
      hs hzero
  constructor
  · intro hstructural
    have hkernel := hfrontier'.1 hstructural
    have hradialZero :
        canonicalCompletedC3MixedRadialGreenKernel s s hs.1
            (by
              simpa [reflectedParameter] using sub_pos.mpr hs.2) = 0 := by
      rw [hrawZero] at hkernel
      exact hkernel.symm
    exact
      (canonicalCompletedC3MixedRadialGreenKernel_self_eq_zero_iff hs).1
        hradialZero
  · intro hcritical
    apply hfrontier'.2
    rw [hrawZero]
    exact
      ((canonicalCompletedC3MixedRadialGreenKernel_self_eq_zero_iff hs).2
        hcritical).symm

/-- Off the critical line, the retained structural triple at a Genuine zero
cannot tend to zero. -/
theorem canonicalC3FiniteMixedHeightStructuralDefect_not_tendsto_zero_of_offCritical_genuineZero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    ¬ Tendsto
      (fun M : ℕ => canonicalC3FiniteMixedHeightStructuralDefect M s s)
      atTop (nhds 0) := by
  intro hstructural
  exact hoff
    ((canonicalC3FiniteMixedHeightStructuralDefect_tendsto_zero_at_genuineZero_iff
      hs hzero).1 hstructural)

/-- The weighted radial Green channel converges to its all-cutoff Hilbert
Gram kernel. -/
theorem finiteFNegFPrimeRadialGreenChannel_tendsto_completed
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ =>
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels M z w).radialGreen)
      atTop
      (nhds
        (mixedHermitianWeight nativeXiCompletionFactor z w *
          canonicalCompletedC3MixedRadialGreenKernel
            (operatorHeightParameter z) (operatorHeightParameter w)
            hw.1
            (by
              simpa [reflectedParameter] using sub_pos.mpr hz.2))) := by
  have hgreen := finiteC3MixedRadialGreen_tendsto_completed
    (z := operatorHeightParameter z)
    (w := operatorHeightParameter w)
    hw.1
    (by simpa [reflectedParameter] using sub_pos.mpr hz.2)
  exact (hgreen.const_mul
    (mixedHermitianWeight nativeXiCompletionFactor z w)).congr'
      (Eventually.of_forall fun M => by
        rfl)

/-- The independently retained weighted tail channel disappears in
completion. -/
theorem finiteFNegFPrimeTailCompletionChannel_tendsto_zero
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ =>
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels M z w).tailCompletion)
      atTop (nhds 0) := by
  have htail := canonicalC3MixedHeightTailCompletionDefect_tendsto_zero
    hz.1 hw.1
  have hweighted : Tendsto
      (fun M : ℕ =>
        mixedHermitianWeight nativeXiCompletionFactor z w *
          canonicalC3MixedHeightTailCompletionDefect M z w)
      atTop (nhds 0) := by
    simpa using htail.const_mul
      (mixedHermitianWeight nativeXiCompletionFactor z w)
  exact hweighted.congr'
      (Eventually.of_forall fun M => by
        rfl)

/-- Candidate global Green kernel obtained from the completed radial Gram
channel and the separately retained archimedean/chart channel. -/
def canonicalCompletedC3FNegFPrimeMixedGreenKernel
    (z w : ℂ)
    (hw : 0 < (operatorHeightParameter w).re)
    (hzReflected :
      0 < (reflectedParameter (operatorHeightParameter z)).re) : ℂ :=
  mixedHermitianWeight nativeXiCompletionFactor z w *
      canonicalCompletedC3MixedRadialGreenKernel
        (operatorHeightParameter z) (operatorHeightParameter w)
        hw hzReflected +
    canonicalCompletedC3ArchimedeanChartMixedChannel z w

/-- Exact reduction of the desired global Green--Wronskian identity.  The
identity holds precisely when the already explicit structural triple tends
to zero, equivalently when the completed raw Wronskian equals the completed
radial Gram kernel. -/
theorem completedFNegFPrimeWronskian_eq_globalGreenKernel_iff
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    mixedHermitianWeight canonicalC3ChartFactorHeight z w *
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
          z w =
      canonicalCompletedC3FNegFPrimeMixedGreenKernel z w hw.1
        (by simpa [reflectedParameter] using sub_pos.mpr hz.2) ↔
    canonicalCompletedC3RawHeightMixedWronskian z w =
      canonicalCompletedC3MixedRadialGreenKernel
        (operatorHeightParameter z) (operatorHeightParameter w)
        hw.1
        (by simpa [reflectedParameter] using sub_pos.mpr hz.2) := by
  have hxiWeight :
      mixedHermitianWeight nativeXiCompletionFactor z w ≠ 0 := by
    unfold mixedHermitianWeight
    exact mul_ne_zero (nativeXiCompletionFactor_ne_zero hz) (by
      simpa using nativeXiCompletionFactor_ne_zero hw)
  rw [completedFNegFPrimeWronskian_crossedChartIdentity hz hw]
  unfold canonicalCompletedC3FNegFPrimeMixedGreenKernel
  constructor
  · intro hidentity
    apply mul_left_cancel₀ hxiWeight
    exact add_right_cancel hidentity
  · intro hidentity
    rw [hidentity]

/-- Equivalent limit formulation of the same global frontier. -/
theorem completedFNegFPrimeWronskian_eq_globalGreenKernel_iff_structural_tendsto_zero
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    mixedHermitianWeight canonicalC3ChartFactorHeight z w *
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
          z w =
      canonicalCompletedC3FNegFPrimeMixedGreenKernel z w hw.1
        (by simpa [reflectedParameter] using sub_pos.mpr hz.2) ↔
    Tendsto
      (fun M : ℕ =>
        canonicalC3FiniteMixedHeightStructuralDefect M
          (operatorHeightParameter z) (operatorHeightParameter w))
      atTop (nhds 0) := by
  rw [completedFNegFPrimeWronskian_eq_globalGreenKernel_iff hz hw]
  have hlimit := canonicalC3FiniteMixedHeightStructuralDefect_tendsto hz hw
  constructor
  · intro hkernel
    rw [hkernel] at hlimit
    simpa using hlimit
  · intro hzero
    exact sub_eq_zero.mp (tendsto_nhds_unique hlimit hzero)

end

end CarrySelfAdjointOperator
