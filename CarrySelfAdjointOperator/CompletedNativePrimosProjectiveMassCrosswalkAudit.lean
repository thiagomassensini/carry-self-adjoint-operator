import CarrySelfAdjointOperator.CompletedNativeProjectiveChiralLosslessDilationAudit
import CarrySelfAdjointOperator.CompletedNativeProjectiveValveMassAudit
import CPFormal.Analytic.CpC2LogJetGpreLift
import CPFormal.Analytic.CpMinimalProvenanceQuotient
import CPFormal.Analytic.CpNativeCarryRealPrecompressionBoundaryWitness
import CPFormal.Analytic.CpNativeGpreFiniteGluedGreenDefect
import CPFormal.Analytic.CpNativeGpreHilbertGluedGreenDefect
import CPFormal.Analytic.CpNativeGpreTfvdProjectiveAnalysis
import CPFormal.Analytic.CpGenuineGprePrimeVerticalTraceAtlas
import CPFormal.Analytic.CpGenuinePrimeCarryDefectUniformBound
import CPFormal.Analytic.CpTfvdSeededFiniteBesselConservation
import CPFormal.Analytic.CpTfvdSameEdgeCompletedPrecompressionCollapse
import CPFormal.Analytic.CpTfvdSameEdgeReflectedEnergyCollapse
import CPFormal.Analytic.CpTfvdSameEdgeReflectedEnergyFixedTimeNoGo

/-!
# Crosswalk of the native `CPFormal` / `primos` projective sources

This module records the concrete material found in the upstream
`CPFormal`/`primos` package.  It is intentionally a crosswalk, not a new
positivity construction.

The package contains four useful structures:

* `DiscreteProjective.reconstructionEquiv` (audited locally) is an exact
  algebraic reconstruction by two affine boundary coordinates and a
  normalized projective mass; the mass alone is not injective.
* `NativeGpreTfvdCompletedPrecompressionSource` is an actual two-slot state.
  On the canonical same-edge input its first slot is zero and its second slot
  is the retained reflected Green-energy state, which is nonzero on the
  critical strip.
* `NativeCarryRealPrecompressionBoundaryWitness` retains the uncompressed
  native state and proves its inverse-carry-mass energy, but its first output
  is a camera/precompression boundary datum, not the chiral output `Q v`.
* the Hilbert gluing theorem cancels the provenance Green terms and leaves the
  vertical Wronskian.  This is a skew boundary identity, not a positive
  polarized conservation law.

The aliases below make those facts available to the current audit.  They
close the source classification requested by the projective/chiral search:
the `primos` carriers provide reconstruction, provenance, and retained
energy, but no second output whose inner products are the Pick defect and no
first output equal to the completed chiral multiplier on the radial Cauchy
carrier.

Carrier status after the ambient and literal-carrier audits:

* BR2 literal: NO-GO;
* Gamma literal: NO-GO;
* normalized ambient Gram literal: NO-GO;
* projective/chiral defect channel: OPEN (the native channels below are
  reconstruction/provenance candidates, not yet a Pick realization).

No square root of `I - T* T`, Kolmogorov/RKHS factorization, Cholesky,
Stieltjes positivity, Jacobi conclusion, zero hypothesis, proof placeholder,
or additional foundational assumption is used here.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

/-! ## The concrete two-channel precompression source -/

theorem canonicalPrimosCompletedPrecompressionSource_first_output_eq_zero
    (M : ℕ) (s : ℂ) :
    (CPFormal.Analytic.Cp.seededTfvdGpreCompletedPrecompressionSource
      (CPFormal.Analytic.Cp.nativeGpreTfvdSameEdgeCompletedPrecompressionCollapseAt
        (3 * M)) M s).1 = 0 := by
  rw [CPFormal.Analytic.Cp.seededTfvdGpreCompletedPrecompressionSource_sameEdge]

theorem canonicalPrimosCompletedPrecompressionSource_second_output_eq_greenEnergy
    (M : ℕ) (s : ℂ) :
    (CPFormal.Analytic.Cp.seededTfvdGpreCompletedPrecompressionSource
      (CPFormal.Analytic.Cp.nativeGpreTfvdSameEdgeCompletedPrecompressionCollapseAt
        (3 * M)) M s).2 =
      CPFormal.Analytic.Cp.nativeGpreGreenEnergyFirstLevelState (3 * M) s := by
  rw [CPFormal.Analytic.Cp.seededTfvdGpreCompletedPrecompressionSource_sameEdge]

theorem canonicalPrimosCompletedPrecompressionSource_second_output_ne_zero
    {M : ℕ} (hM : 0 < M) {s : ℂ}
    (hs : s ∈ CPFormal.Analytic.Cp.genuineCriticalStrip) :
    (CPFormal.Analytic.Cp.seededTfvdGpreCompletedPrecompressionSource
      (CPFormal.Analytic.Cp.nativeGpreTfvdSameEdgeCompletedPrecompressionCollapseAt
        (3 * M)) M s).2 ≠ 0 := by
  rw [canonicalPrimosCompletedPrecompressionSource_second_output_eq_greenEnergy]
  exact CPFormal.Analytic.Cp.nativeGpreGreenEnergyFirstLevelState_ne_zero
    (M := 3 * M) (by omega) hs

theorem canonicalPrimosCompletedPrecompressionSource_point_blind_at_critical
    {M : ℕ} (hM : 0 < M) {s : ℂ}
    (hs : s ∈ CPFormal.Analytic.Cp.genuineCriticalStrip)
    (hcritical : CPFormal.Analytic.Cp.criticalDisplacement s.re = 0) :
    (∀ p : Nat.Primes,
      CPFormal.Analytic.Cp.nativeGpreTfvdCompletedPrecompressionPrimeReadout p s
        (CPFormal.Analytic.Cp.seededTfvdGpreCompletedPrecompressionSource
          (CPFormal.Analytic.Cp.nativeGpreTfvdSameEdgeCompletedPrecompressionCollapseAt
            (3 * M)) M s) = 0) ∧
      CPFormal.Analytic.Cp.seededTfvdGpreCompletedPrecompressionSource
        (CPFormal.Analytic.Cp.nativeGpreTfvdSameEdgeCompletedPrecompressionCollapseAt
          (3 * M)) M s ≠ 0 := by
  exact CPFormal.Analytic.Cp.completedSameEdgePrecompression_pointBlindAtCritical
    hM hs hcritical

/-! ## The retained precompression witness and projective mass -/

theorem canonicalPrimosPrecompressionWitness_energy_eq_inverse_mass
    {time : ℝ}
    (W : CPFormal.Analytic.Cp.NativeCarryRealPrecompressionBoundaryWitness time)
    {n : ℤ} (hn : 0 < n) :
    CPFormal.Analytic.Cp.nativeCarryRealPlaneEnergy (W.state n) = ((n : ℝ))⁻¹ :=
  W.state_energy_eq_inverse hn

theorem canonicalPrimosPrecompressionLift_forces_critical_exponent
    {sigma time : ℝ}
    (hlift :
      CPFormal.Analytic.Cp.NativeCarryRealPlaneBoundaryClosureHasPrecompressionLift
        sigma time) :
    sigma = (1 : ℝ) / 2 :=
  CPFormal.Analytic.Cp.boundaryClosurePrecompressionLift_sigma_eq_half hlift

/-! ## What the Hilbert gluing actually conserves -/

theorem canonicalPrimosGluedHilbertGreenDefect_eq_verticalWronskian
    (q : ℝ) (S : Finset CPFormal.Analytic.Cp.NativeGpreBoundaryContext)
    (x y : CPFormal.Analytic.Cp.NativeGpreComplexEdgeCore) :
    inner ℂ
        ((CPFormal.Analytic.Cp.nativeGpreFiniteGluedHilbertBoundaryPencil q S).fluxTrace y)
        ((CPFormal.Analytic.Cp.nativeGpreFiniteGluedHilbertBoundaryPencil q S).valueTrace x) -
      inner ℂ
        ((CPFormal.Analytic.Cp.nativeGpreFiniteGluedHilbertBoundaryPencil q S).valueTrace y)
        ((CPFormal.Analytic.Cp.nativeGpreFiniteGluedHilbertBoundaryPencil q S).fluxTrace x) =
      CPFormal.Analytic.Cp.carryWeightedVerticalBoundaryWronskian q
        (CPFormal.Analytic.Cp.nativeGpreCanonicalVerticalRealization x)
        (CPFormal.Analytic.Cp.nativeGpreCanonicalVerticalRealization y) :=
  CPFormal.Analytic.Cp.nativeGpreFiniteGluedHilbertGreenDefect_eq_verticalWronskian
    q S x y

/-! ## Enriched reconstruction is exact, but not an energy balance -/

theorem canonicalPrimosC2LogJet_enriched_reconstruction
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset CPFormal.Analytic.Cp.NativeGpreBoundaryContext)
    (s : ℂ) (N : ℕ) :
    CPFormal.Analytic.Cp.nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
        (CPFormal.Analytic.Cp.c2LogJetPrefixEnrichedAnalysis q S s N) =
      CPFormal.Analytic.Cp.nativeGpreCanonicalVerticalRealization
        (CPFormal.Analytic.Cp.c2LogJetPrefixCore s N) :=
  CPFormal.Analytic.Cp.c2LogJetPrefixEnrichedAnalysis_reconstruction
    q hqpos hq1 S s N

/-! ## The native ordinary/log-jet two-layer lift

The same-edge source in `primos` is the closest existing lossless-looking
projective construction.  Its two coordinates are not invented here: they
are the ordinary Dirichlet gradient and its logarithmic jet.  The recovery
theorems invert that pair before any prime or Green readout is taken.  This
is the correct algebraic analogue of retaining an incident coordinate and a
second channel; it is deliberately not identified with the chiral quotient
`Q`.
-/

/-- The ordinary/log-jet two-coordinate map is injective on each edge.  The
proof uses the native recovery formulas for both endpoints, rather than a
dimension count or an abstract quotient. -/
theorem canonicalPrimosSameEdgeOrdinaryLogJet_readout_injective
    (n : ℕ) :
    Function.Injective (fun endpoints : ℂ × ℂ =>
      (endpoints.2 - endpoints.1,
      (Real.log (((n + 2 : ℕ) : ℝ)) : ℂ) * endpoints.2 -
          (Real.log (((n + 1 : ℕ) : ℝ)) : ℂ) * endpoints.1)) := by
  intro x y hxy
  have hdiff : x.2 - x.1 = y.2 - y.1 := by
    exact congrArg Prod.fst hxy
  have hlog :
      (Real.log (((n + 2 : ℕ) : ℝ)) : ℂ) * x.2 -
          (Real.log (((n + 1 : ℕ) : ℝ)) : ℂ) * x.1 =
        (Real.log (((n + 2 : ℕ) : ℝ)) : ℂ) * y.2 -
          (Real.log (((n + 1 : ℕ) : ℝ)) : ℂ) * y.1 := by
    exact congrArg Prod.snd hxy
  apply Prod.ext
  · calc
      x.1 = CPFormal.Analytic.Cp.sameEdgeRecoverLeft n
          (x.2 - x.1)
          ((Real.log (((n + 2 : ℕ) : ℝ)) : ℂ) * x.2 -
            (Real.log (((n + 1 : ℕ) : ℝ)) : ℂ) * x.1) :=
        (CPFormal.Analytic.Cp.sameEdgeRecoverLeft_of_values n x.1 x.2).symm
      _ = CPFormal.Analytic.Cp.sameEdgeRecoverLeft n
          (y.2 - y.1)
          ((Real.log (((n + 2 : ℕ) : ℝ)) : ℂ) * y.2 -
            (Real.log (((n + 1 : ℕ) : ℝ)) : ℂ) * y.1) := by
        rw [hdiff, hlog]
      _ = y.1 :=
        CPFormal.Analytic.Cp.sameEdgeRecoverLeft_of_values n y.1 y.2
  · calc
      x.2 = CPFormal.Analytic.Cp.sameEdgeRecoverRight n
          (x.2 - x.1)
          ((Real.log (((n + 2 : ℕ) : ℝ)) : ℂ) * x.2 -
            (Real.log (((n + 1 : ℕ) : ℝ)) : ℂ) * x.1) :=
        (CPFormal.Analytic.Cp.sameEdgeRecoverRight_of_values n x.1 x.2).symm
      _ = CPFormal.Analytic.Cp.sameEdgeRecoverRight n
          (y.2 - y.1)
          ((Real.log (((n + 2 : ℕ) : ℝ)) : ℂ) * y.2 -
            (Real.log (((n + 1 : ℕ) : ℝ)) : ℂ) * y.1) := by
        rw [hdiff, hlog]
      _ = y.2 :=
        CPFormal.Analytic.Cp.sameEdgeRecoverRight_of_values n y.1 y.2

/-- The canonical ordinary/log-jet pair recovers both spectral endpoints and
then the reflected gradient.  These are exact geometric identities before
any moment or positivity statement. -/
theorem canonicalPrimosSameEdgeOrdinaryLogJet_reflectedGradient_exact
    (s : ℂ) (n : ℕ) :
    CPFormal.Analytic.Cp.sameEdgeRecoveredReflectedGradient n
        (CPFormal.Analytic.Cp.positiveDirichletGradient s n)
        (CPFormal.Analytic.Cp.positiveLogDirichletGradient s n) =
      CPFormal.Analytic.Cp.positiveDirichletGradient
        (CPFormal.Analytic.Cp.reflectedParameter s) n :=
  CPFormal.Analytic.Cp.sameEdgeRecoveredReflectedGradient_canonical s n

/-- The second native output retained by this two-layer lift is the reflected
Green edge energy.  It is a provenance channel, not a Pick defect channel. -/
theorem canonicalPrimosSameEdgeOrdinaryLogJet_reflectedEnergy_exact
    (s : ℂ) (n : ℕ) :
    CPFormal.Analytic.Cp.sameEdgeRecoveredReflectedEnergyEdge n
        (CPFormal.Analytic.Cp.positiveDirichletGradient s n)
        (CPFormal.Analytic.Cp.positiveLogDirichletGradient s n) =
      (CPFormal.Analytic.Cp.finiteReflectedGradientEdge n s).re :=
  CPFormal.Analytic.Cp.sameEdgeRecoveredReflectedEnergyEdge_canonical s n

/-- After the explicit ordinary/log-jet recovery, the remaining all-prime
identification is exactly the reflected-profile-to-fixed-time transport gate.
This names the first open material condition; it is not hidden in a mass
normalization. -/
theorem canonicalPrimosSameEdgeOrdinaryLogJet_fixedTime_gate_iff
    (M : ℕ) (s : ℂ) :
    CPFormal.Analytic.Cp.IsSeededTfvdGpreMomentCollapseAt
        (CPFormal.Analytic.Cp.nativeGpreTfvdSameEdgeReflectedEnergyCollapseAt
          (3 * M)) M s ↔
      CPFormal.Analytic.Cp.SameEdgeReflectedEnergyTransportsToFixedTimeAt M s :=
  CPFormal.Analytic.Cp.isSeededTfvdGpreMomentCollapseAt_sameEdgeReflectedEnergy_iff
    M s

/-- On the critical locus the raw reflected-energy output cannot pass the
fixed-time gate: its reflected-profile readout is zero while the native
fixed-time level-one readout is strictly positive.  This is a native
candidate-specific no-go, not a no-go for projective/chiral dilations in
general. -/
theorem canonicalPrimosSameEdgeOrdinaryLogJet_fixedTime_gate_not_of_critical
    (p : Nat.Primes) {M : ℕ} (hM : 0 < M)
    {s : ℂ} (hs : CPFormal.Analytic.Cp.genuineCriticalStrip s)
    (hcritical : CPFormal.Analytic.Cp.criticalDisplacement s.re = 0) :
    ¬ CPFormal.Analytic.Cp.IsSeededTfvdGpreMomentCollapseAt
        (CPFormal.Analytic.Cp.nativeGpreTfvdSameEdgeReflectedEnergyCollapseAt
          (3 * M)) M s :=
  CPFormal.Analytic.Cp.isSeededTfvdGpreMomentCollapseAt_sameEdgeReflectedEnergy_not_of_critical
    p hM hs hcritical

theorem canonicalPrimosSameEdgeOrdinaryLogJet_critical_reflected_readout_eq_zero
    (p : Nat.Primes) (M : ℕ) (s : ℂ)
    (hcritical : CPFormal.Analytic.Cp.criticalDisplacement s.re = 0) :
    inner ℝ (CPFormal.Analytic.Cp.nativeGpreReflectedFirstLevelGapProfile p s)
        (CPFormal.Analytic.Cp.seededTfvdGpreCollapsedSource
          (CPFormal.Analytic.Cp.nativeGpreTfvdSameEdgeReflectedEnergyCollapseAt
            (3 * M)) M s) = 0 :=
  CPFormal.Analytic.Cp.inner_nativeGpreReflectedFirstLevelGapProfile_seededSameEdgeCollapsedSource_eq_zero_of_critical
    M p s hcritical

theorem canonicalPrimosSameEdgeOrdinaryLogJet_critical_fixed_time_readout_pos
    (p : Nat.Primes) {M : ℕ} (hM : 0 < M)
    {s : ℂ} (hs : CPFormal.Analytic.Cp.genuineCriticalStrip s) :
    0 < inner ℝ (CPFormal.Analytic.Cp.nativeGpreTowerProfileVector (p : ℕ) 1)
        (CPFormal.Analytic.Cp.seededTfvdGpreCollapsedSource
          (CPFormal.Analytic.Cp.nativeGpreTfvdSameEdgeReflectedEnergyCollapseAt
            (3 * M)) M s) :=
  by
    rw [CPFormal.Analytic.Cp.seededTfvdGpreCollapsedSource_sameEdgeReflectedEnergy]
    exact CPFormal.Analytic.Cp.inner_nativeGpreTowerProfileVector_greenEnergyFirstLevelState_pos
      p (M := 3 * M) (by omega) hs

/-! The preceding two readouts expose the exact first residual of this
candidate: at critical displacement it is `positive - 0`, before any
all-prime or Pick positivity argument. -/
theorem canonicalPrimosSameEdgeOrdinaryLogJet_critical_fixed_time_residual_pos
    (p : Nat.Primes) {M : ℕ} (hM : 0 < M)
    {s : ℂ} (hs : CPFormal.Analytic.Cp.genuineCriticalStrip s)
    (hcritical : CPFormal.Analytic.Cp.criticalDisplacement s.re = 0) :
    0 <
      inner ℝ (CPFormal.Analytic.Cp.nativeGpreTowerProfileVector (p : ℕ) 1)
          (CPFormal.Analytic.Cp.seededTfvdGpreCollapsedSource
            (CPFormal.Analytic.Cp.nativeGpreTfvdSameEdgeReflectedEnergyCollapseAt
              (3 * M)) M s) -
        inner ℝ (CPFormal.Analytic.Cp.nativeGpreReflectedFirstLevelGapProfile p s)
          (CPFormal.Analytic.Cp.seededTfvdGpreCollapsedSource
            (CPFormal.Analytic.Cp.nativeGpreTfvdSameEdgeReflectedEnergyCollapseAt
              (3 * M)) M s) := by
  have hfixed :=
    canonicalPrimosSameEdgeOrdinaryLogJet_critical_fixed_time_readout_pos
      p hM hs
  have hreflected :=
    canonicalPrimosSameEdgeOrdinaryLogJet_critical_reflected_readout_eq_zero
      p M s hcritical
  linarith

/-- The enriched C2 log-jet analysis also has an exact TFVD left inverse and
retains its two provenance roles.  This is a genuine native reconstruction,
but the proved readout is the log-jet scalar rather than `Qv`, and no norm
conservation theorem is present in the source package. -/
theorem canonicalPrimosC2LogJet_enriched_scalar_readout_exact
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset CPFormal.Analytic.Cp.NativeGpreBoundaryContext)
    (s : ℂ) (N : ℕ) :
    CPFormal.Analytic.Cp.c2LogJetPrefixEnrichedReadout
        q hqpos.le hq1 S N
        (CPFormal.Analytic.Cp.c2LogJetPrefixEnrichedAnalysis q S s N) =
      CPFormal.Analytic.Cp.positiveLogDirichletValue s N :=
  CPFormal.Analytic.Cp.c2LogJetPrefixEnrichedReadout_analysis
    q hqpos hq1 S s N

/-! ## The full projective TFVD--`G_pre` output

The package also contains a genuinely projective family of all finite
provenance atlases.  Its first output is still the native TFVD bracket--trace
pair, while the second output records the two `G_pre` provenance roles.  The
projective reconstruction reads the empty-atlas TFVD component and is an
exact left inverse.  This is an algebraic reconstruction statement; no norm
balance is asserted for the four displayed output slots.
-/

theorem canonicalPrimosProjectiveAnalysis_compatible
    (q : ℝ) (x : CPFormal.Analytic.Cp.CarryVerticalL2) :
    CPFormal.Analytic.Cp.NativeGpreTfvdProjectiveCompatible
      (CPFormal.Analytic.Cp.nativeGpreTfvdProjectiveAnalysis q x) :=
  CPFormal.Analytic.Cp.nativeGpreTfvdProjectiveAnalysis_compatible q x

theorem canonicalPrimosProjectiveAnalysis_first_output_eq_bracket
    (q : ℝ) (S : Finset CPFormal.Analytic.Cp.NativeGpreBoundaryContext)
    (x : CPFormal.Analytic.Cp.CarryVerticalL2) :
    (CPFormal.Analytic.Cp.nativeGpreTfvdProjectiveAnalysis q x S).1.1 =
      CPFormal.Analytic.Cp.carryWeightedVerticalCenteredBracket q x := by
  rfl

theorem canonicalPrimosProjectiveAnalysis_first_output_eq_trace
    (q : ℝ) (S : Finset CPFormal.Analytic.Cp.NativeGpreBoundaryContext)
    (x : CPFormal.Analytic.Cp.CarryVerticalL2) :
    (CPFormal.Analytic.Cp.nativeGpreTfvdProjectiveAnalysis q x S).1.2 =
      CPFormal.Analytic.Cp.carryWeightedVerticalTrace q x := by
  rfl

theorem canonicalPrimosProjectiveAnalysis_second_output_eq_provenance
    (q : ℝ) (S : Finset CPFormal.Analytic.Cp.NativeGpreBoundaryContext)
    (x : CPFormal.Analytic.Cp.CarryVerticalL2) :
    (CPFormal.Analytic.Cp.nativeGpreTfvdProjectiveAnalysis q x S).2 =
      (CPFormal.Analytic.Cp.nativeGpreFiniteContinuousBoundaryValueLift S x,
        CPFormal.Analytic.Cp.nativeGpreFiniteContinuousBoundaryNumberFluxLift S x) := by
  rfl

theorem canonicalPrimosProjectiveAnalysis_reconstruction_exact
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (x : CPFormal.Analytic.Cp.CarryVerticalL2) :
    CPFormal.Analytic.Cp.nativeGpreTfvdProjectiveReconstruction q hqpos.le hq1
        (CPFormal.Analytic.Cp.nativeGpreTfvdProjectiveAnalysis q x) = x :=
  CPFormal.Analytic.Cp.nativeGpreTfvdProjectiveReconstruction_analysis
    q hqpos hq1 x

theorem canonicalPrimosProjectiveAnalysis_reconstruction_is_green_add_return
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (data : CPFormal.Analytic.Cp.NativeGpreTfvdProjectiveAnalysisCarrier) :
    CPFormal.Analytic.Cp.nativeGpreTfvdProjectiveReconstruction q hq0 hq1 data =
      CPFormal.Analytic.Cp.carryVerticalL2WeightedGreen q
          (data (∅ : Finset CPFormal.Analytic.Cp.NativeGpreBoundaryContext)).1.1 +
        CPFormal.Analytic.Cp.carryWeightedVerticalReturn q hq0 hq1
          (data (∅ : Finset CPFormal.Analytic.Cp.NativeGpreBoundaryContext)).1.2 := by
  rfl

theorem canonicalPrimosProjectiveAnalysis_injective
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    Function.Injective (CPFormal.Analytic.Cp.nativeGpreTfvdProjectiveAnalysis q) :=
  CPFormal.Analytic.Cp.nativeGpreTfvdProjectiveAnalysis_injective q hqpos hq1

/-! ## The strongest positive prime-wise output

The prime vertical-trace atlas is a real Hilbert state with an exact norm
ledger.  Its trace has zero value coordinate and Green bulk flux.  This is a
genuine positive output, but it belongs to the provenance/energy channel: no
theorem identifies it with the projective multiplier output `Q v` or with a
polarized Pick defect.
-/

theorem canonicalPrimosPrimeMassFiber_trace_eq_zero_greenBulk
    (M : ℕ) (s : ℂ) (p : Nat.Primes) :
    CPFormal.Analytic.Cp.primeCarryWeightedVerticalTrace (p : ℕ)
        (CPFormal.Analytic.Cp.primeMassGreenVerticalFiberState M s p) =
      (0, (CPFormal.Analytic.Cp.primeCarryGreenBulkCutoffProfile M s p : ℂ)) :=
  CPFormal.Analytic.Cp.primeCarryWeightedVerticalTrace_massFiber M s p

theorem canonicalPrimosPrimeMassTraceFiniteState_norm_sq
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    ‖CPFormal.Analytic.Cp.primeMassGreenVerticalTraceFiniteState M s S‖ ^ 2 =
      ∑ p ∈ S,
        (CPFormal.Analytic.Cp.primeMassGreenVerticalTraceFluxProfile M s p) ^ 2 :=
  CPFormal.Analytic.Cp.primeMassGreenVerticalTraceFiniteState_norm_sq M s S

theorem canonicalPrimosPrimeMassTraceFiniteState_eq_greenBulk
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    CPFormal.Analytic.Cp.primeMassGreenVerticalTraceFiniteState M s S =
      CPFormal.Analytic.Cp.primeGreenBulkFiniteState M s S :=
  CPFormal.Analytic.Cp.primeMassGreenVerticalTraceFiniteState_eq_greenBulkFiniteState
    M s S

/-! ## The closest positive lossless channel in `primos`

The prime-carry provenance package does contain the kind of conservation law
we were looking for, but for a different first output.  A state `x` realizing
the active enriched prime readouts splits orthogonally into the canonical
centered-carry provenance state and an unused residual.  The active term is
also exactly the seeded TFVD Bessel energy.  These identities are therefore a
genuine lossless dilation of the *provenance/readout* map.  Nothing in the
package identifies that map with the radial chiral multiplier `Q`, so these
aliases are recorded as a positive partial channel rather than as a Pick
defect realization.
-/

theorem canonicalPrimosPrimeCarryProvenance_pythagoras_of_realizesOn
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes)
    (x : CPFormal.Analytic.Cp.PrimeCarryDefectGlobalHilbert)
    (hrealizes :
      CPFormal.Analytic.Cp.IsCanonicalEnrichedPrimeCarryDefectReadoutRealizationOn
        M s S x) :
    ‖x‖ ^ 2 =
      ‖CPFormal.Analytic.Cp.canonicalEnrichedPrimeCarryDefectProvenanceState
          M s S‖ ^ 2 +
        ‖x -
          CPFormal.Analytic.Cp.canonicalEnrichedPrimeCarryDefectProvenanceState
            M s S‖ ^ 2 :=
  CPFormal.Analytic.Cp.canonicalProvenanceState_pythagoras_of_realizesOn
    M s S x hrealizes

theorem canonicalPrimosPrimeCarryProvenance_residual_orthogonal_of_realizesOn
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes)
    (x : CPFormal.Analytic.Cp.PrimeCarryDefectGlobalHilbert)
    (hrealizes :
      CPFormal.Analytic.Cp.IsCanonicalEnrichedPrimeCarryDefectReadoutRealizationOn
        M s S x) :
    inner ℝ
        (CPFormal.Analytic.Cp.canonicalEnrichedPrimeCarryDefectProvenanceState
          M s S)
        (x -
          CPFormal.Analytic.Cp.canonicalEnrichedPrimeCarryDefectProvenanceState
            M s S) = 0 :=
  CPFormal.Analytic.Cp.inner_canonicalProvenanceState_residual_eq_zero_of_realizesOn
    M s S x hrealizes

theorem canonicalPrimosSeededTfvdBessel_pythagoras_of_realizesOn
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes)
    (x : CPFormal.Analytic.Cp.PrimeCarryDefectGlobalHilbert)
    (hrealizes :
      CPFormal.Analytic.Cp.IsCanonicalEnrichedPrimeCarryDefectReadoutRealizationOn
        M s S x) :
    ‖x‖ ^ 2 =
      CPFormal.Analytic.Cp.finiteSeededTfvdBesselEnergy M s S +
        ‖x -
          CPFormal.Analytic.Cp.canonicalEnrichedPrimeCarryDefectProvenanceState
            M s S‖ ^ 2 :=
  CPFormal.Analytic.Cp.canonicalProvenanceState_pythagoras_seededTfvdBesselLedger_of_realizesOn
    M s S x hrealizes

/-!
The provenance Pythagoras has a genuinely polarized form.  If two states
realize the same finite prime-atlas readouts, the canonical active state is
the common first output and the two residuals are the second output.  This is
the exact sesquilinear conservation law available from the `primos` carrier;
it is deliberately not identified with the radial chiral multiplier.
-/
theorem canonicalPrimosPrimeCarryProvenance_polarized_pythagoras_of_realizesOn
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes)
    (x y : CPFormal.Analytic.Cp.PrimeCarryDefectGlobalHilbert)
    (hx :
      CPFormal.Analytic.Cp.IsCanonicalEnrichedPrimeCarryDefectReadoutRealizationOn
        M s S x)
    (hy :
      CPFormal.Analytic.Cp.IsCanonicalEnrichedPrimeCarryDefectReadoutRealizationOn
        M s S y) :
    inner ℝ x y =
      ‖CPFormal.Analytic.Cp.canonicalEnrichedPrimeCarryDefectProvenanceState
          M s S‖ ^ 2 +
        inner ℝ
          (x - CPFormal.Analytic.Cp.canonicalEnrichedPrimeCarryDefectProvenanceState
            M s S)
          (y - CPFormal.Analytic.Cp.canonicalEnrichedPrimeCarryDefectProvenanceState
            M s S) := by
  let P : CPFormal.Analytic.Cp.PrimeCarryDefectGlobalHilbert :=
    CPFormal.Analytic.Cp.canonicalEnrichedPrimeCarryDefectProvenanceState
      M s S
  let Rₓ : CPFormal.Analytic.Cp.PrimeCarryDefectGlobalHilbert := x - P
  let Rᵧ : CPFormal.Analytic.Cp.PrimeCarryDefectGlobalHilbert := y - P
  have hPₓ : inner ℝ P Rₓ = 0 := by
    dsimp [P, Rₓ]
    exact
      CPFormal.Analytic.Cp.inner_canonicalProvenanceState_residual_eq_zero_of_realizesOn
        M s S x hx
  have hPᵧ : inner ℝ P Rᵧ = 0 := by
    dsimp [P, Rᵧ]
    exact
      CPFormal.Analytic.Cp.inner_canonicalProvenanceState_residual_eq_zero_of_realizesOn
        M s S y hy
  have hₓP : inner ℝ Rₓ P = 0 := by
    rw [real_inner_comm]
    exact hPₓ
  have hx_decomp : x = P + Rₓ := by
    dsimp [Rₓ]
    abel
  have hy_decomp : y = P + Rᵧ := by
    dsimp [Rᵧ]
    abel
  calc
    inner ℝ x y = inner ℝ (P + Rₓ) (P + Rᵧ) := by rw [hx_decomp, hy_decomp]
    _ = (inner ℝ P P + inner ℝ P Rᵧ) +
        (inner ℝ Rₓ P + inner ℝ Rₓ Rᵧ) := by
      rw [inner_add_left, inner_add_right, inner_add_right]
    _ = ‖P‖ ^ 2 + inner ℝ Rₓ Rᵧ := by
      rw [hPᵧ, hₓP, real_inner_self_eq_norm_sq]
      ring

/-! The same polarized ledger written with the seeded TFVD/Bessel active term. -/
theorem canonicalPrimosSeededTfvdBessel_polarized_pythagoras_of_realizesOn
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes)
    (x y : CPFormal.Analytic.Cp.PrimeCarryDefectGlobalHilbert)
    (hx :
      CPFormal.Analytic.Cp.IsCanonicalEnrichedPrimeCarryDefectReadoutRealizationOn
        M s S x)
    (hy :
      CPFormal.Analytic.Cp.IsCanonicalEnrichedPrimeCarryDefectReadoutRealizationOn
        M s S y) :
    inner ℝ x y =
      CPFormal.Analytic.Cp.finiteSeededTfvdBesselEnergy M s S +
        inner ℝ
          (x - CPFormal.Analytic.Cp.canonicalEnrichedPrimeCarryDefectProvenanceState
            M s S)
          (y - CPFormal.Analytic.Cp.canonicalEnrichedPrimeCarryDefectProvenanceState
            M s S) := by
  rw [canonicalPrimosPrimeCarryProvenance_polarized_pythagoras_of_realizesOn
    M s S x y hx hy,
    CPFormal.Analytic.Cp.canonicalEnrichedPrimeCarryDefectProvenanceState_norm_sq_eq_finiteSeededTfvdBesselEnergy]

theorem canonicalPrimosNativeMomentRealization_to_contractiveProvenanceState
    (M : ℕ) (s : ℂ)
    (x : CPFormal.Analytic.Cp.NativeGpreTowerHilbert)
    (hx :
      CPFormal.Analytic.Cp.IsNativeGprePrimeMomentRealizationAt
        1 (3 * M) s x) :
    ∃ y : CPFormal.Analytic.Cp.PrimeCarryDefectGlobalHilbert,
      CPFormal.Analytic.Cp.IsCanonicalEnrichedPrimeCarryDefectReadoutRealization
          M s y ∧
        ‖y‖ ^ 2 ≤ (11 / 12 : ℝ) * ‖x‖ ^ 2 :=
  CPFormal.Analytic.Cp.nativeMomentRealization_yields_contractive_globalRealization
    M s x hx

end

end CarrySelfAdjointOperator
