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

No square root of `I - T* T`, Kolmogorov/RKHS factorization, Cholesky,
Stieltjes positivity, Jacobi conclusion, zero hypothesis, `sorry`, `admit`,
or new axiom is used here.
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
