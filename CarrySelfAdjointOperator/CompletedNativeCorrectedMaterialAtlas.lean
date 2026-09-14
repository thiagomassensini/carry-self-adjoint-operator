import CarrySelfAdjointOperator.CompletedNativeCorrectedAtlasConstruction
import CPFormal.Analytic.CpTfvdSameEdgeCompletedPrecompressionCollapse
import CPFormal.Analytic.CpTfvdSameEdgeReflectedEnergyFixedTimeNoGo
import CPFormal.Analytic.CpNativeGpreTfvdCommutatorTowerSource
import Mathlib.Tactic

/-!
# Material realization of the corrected native atlas

The corrected material atlas is the already formalized same-edge
precompression collapse. It has a visible fixed-native-time slot and a
residual reflected-energy slot reconstructed from ordinary and logarithmic
TFVD edge data. The visible slot is not filled by a fitted vector.
-/

open scoped ENNReal InnerProduct lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

abbrev CanonicalCompletedNativeCorrectedMaterialAtlasCarrier :=
  NativeGpreTfvdCompletedPrecompressionSource

def canonicalCompletedNativeCorrectedMaterialAtlasState
    (M : ℕ) (s : ℂ) :
    CanonicalCompletedNativeCorrectedMaterialAtlasCarrier :=
  seededTfvdGpreCompletedPrecompressionSource
    (nativeGpreTfvdSameEdgeCompletedPrecompressionCollapseAt (3 * M))
    M s

def canonicalCompletedNativeCorrectedMaterialAtlasPrimeReadout
    (p : Nat.Primes) (s : ℂ)
    (state : CanonicalCompletedNativeCorrectedMaterialAtlasCarrier) :
    ℝ × ℝ :=
  nativeGpreTfvdCompletedPrecompressionPrimeReadout p s state

theorem canonicalCompletedNativeCorrectedMaterialAtlasState_eq_sameEdge
    (M : ℕ) (s : ℂ) :
    canonicalCompletedNativeCorrectedMaterialAtlasState M s =
      (0, nativeGpreGreenEnergyFirstLevelState (3 * M) s) := by
  exact seededTfvdGpreCompletedPrecompressionSource_sameEdge M s

theorem canonicalCompletedNativeCorrectedMaterialAtlasPrimeReadout_eq_greenBulk
    (M : ℕ) (s : ℂ) (p : Nat.Primes) :
    canonicalCompletedNativeCorrectedMaterialAtlasPrimeReadout p s
        (canonicalCompletedNativeCorrectedMaterialAtlasState M s) =
      (0, primeCarryGreenBulkCutoffProfile (3 * M) s p) := by
  exact nativeGpreTfvdCompletedPrecompressionPrimeReadout_sameEdge M s p

theorem canonicalCompletedNativeCorrectedMaterialAtlas_pointBlindAtCritical
    {M : ℕ} (hM : 0 < M) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hcritical : criticalDisplacement s.re = 0) :
    (∀ p : Nat.Primes,
      canonicalCompletedNativeCorrectedMaterialAtlasPrimeReadout p s
        (canonicalCompletedNativeCorrectedMaterialAtlasState M s) = 0) ∧
      canonicalCompletedNativeCorrectedMaterialAtlasState M s ≠ 0 := by
  exact completedSameEdgePrecompression_pointBlindAtCritical hM hs hcritical

def HasCanonicalCompletedNativeCorrectedMaterialAtlasFixedTimeTransport
    (M : ℕ) (s : ℂ) : Prop :=
  SameEdgeReflectedEnergyTransportsToFixedTimeAt M s

theorem canonicalCompletedNativeCorrectedMaterialAtlasFixedTimeTransport_iff_momentCollapse
    (M : ℕ) (s : ℂ) :
    IsSeededTfvdGpreMomentCollapseAt
        (nativeGpreTfvdSameEdgeReflectedEnergyCollapseAt (3 * M)) M s ↔
      HasCanonicalCompletedNativeCorrectedMaterialAtlasFixedTimeTransport M s := by
  exact isSeededTfvdGpreMomentCollapseAt_sameEdgeReflectedEnergy_iff M s

/-! The raw same-edge reflected-energy source cannot itself be the fixed-time
native moment source on the critical locus: its reflected readout vanishes,
while its fixed native-time readout remains strictly positive. The corrected
atlas therefore has to keep the hidden reflected slot and change the readout,
not identify the raw source with the fixed-time profile. -/
theorem canonicalCompletedNativeCorrectedMaterialAtlasFixedTimeTransport_not_of_critical
    (p : Nat.Primes) {M : ℕ} (hM : 0 < M) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hcritical : criticalDisplacement s.re = 0) :
    ¬ HasCanonicalCompletedNativeCorrectedMaterialAtlasFixedTimeTransport M s := by
  exact sameEdgeReflectedEnergyTransportsToFixedTimeAt_not_of_critical
    p hM hs hcritical

theorem canonicalCompletedNativeCorrectedMaterialAtlasMomentCollapse_not_of_critical
    (p : Nat.Primes) {M : ℕ} (hM : 0 < M) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hcritical : criticalDisplacement s.re = 0) :
    ¬ IsSeededTfvdGpreMomentCollapseAt
        (nativeGpreTfvdSameEdgeReflectedEnergyCollapseAt (3 * M)) M s := by
  exact isSeededTfvdGpreMomentCollapseAt_sameEdgeReflectedEnergy_not_of_critical
    p hM hs hcritical

def canonicalCompletedNativeCorrectedMaterialAtlasPrefixSource
    (p : Nat.Primes) (tau M : ℕ) (s : ℂ) :
    NativeGpreTowerHilbert :=
  nativeGpreCanonicalCpLogJetCommutatorPrefixTowerSource p tau (3 * M) s

theorem inner_canonicalCompletedNativeCorrectedMaterialAtlasPrefixSource_eq_greenBulk
    (p : Nat.Primes) (tau M : ℕ) (s : ℂ) :
    inner ℝ (nativeGpreTowerProfileVector (p : ℕ) tau)
        (canonicalCompletedNativeCorrectedMaterialAtlasPrefixSource p tau M s) =
      finiteNativeGpreLogJetGreenBulkReadout p M s := by
  exact inner_nativeGpreTowerProfileVector_canonicalCpLogJetCommutatorPrefixTowerSource_eq_greenBulk
    p tau M s

end

end CarrySelfAdjointOperator
