import CarrySelfAdjointOperator.CompletedNativeProjectiveChiralLosslessDilationAudit
import CarrySelfAdjointOperator.CompletedNativeProjectiveValveMassAudit
import CPFormal.Analytic.CpC2LogJetGpreLift
import CPFormal.Analytic.CpMinimalProvenanceQuotient
import CPFormal.Analytic.CpNativeCarryRealPrecompressionBoundaryWitness
import CPFormal.Analytic.CpNativeGpreFiniteGluedGreenDefect
import CPFormal.Analytic.CpNativeGpreHilbertGluedGreenDefect
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

end

end CarrySelfAdjointOperator
