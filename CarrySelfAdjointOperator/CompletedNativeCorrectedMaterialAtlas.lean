import CarrySelfAdjointOperator.CompletedNativeCorrectedAtlasConstruction
import CarrySelfAdjointOperator.CompletedNativePolarizedSameEdgeGreenGramBridge
import CarrySelfAdjointOperator.CompletedNativeExpandedStructuralBlockProbe
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
open C3TraceDynamics
open Filter

noncomputable section

abbrev CanonicalCompletedNativeCorrectedMaterialAtlasCarrier :=
  NativeGpreTfvdCompletedPrecompressionSource

def canonicalCompletedNativeCorrectedMaterialAtlasState
    (M : ℕ) (s : ℂ) :
    CanonicalCompletedNativeCorrectedMaterialAtlasCarrier :=
  seededTfvdGpreCompletedPrecompressionSource
    (nativeGpreTfvdSameEdgeCompletedPrecompressionCollapseAt (3 * M))
    M s

/-! ## The corrected radial operation

The existing completed precompression carrier already contains the required
operation: inject the recovered energy into the residual slot while setting
the untransported fixed-time slot to zero. The radial profile is then used
only at readout, where it is annihilated on the critical locus. -/

def canonicalCompletedNativeCorrectedMaterialAtlasRadialInjection
    (energy : NativeGpreTowerHilbert) :
    CanonicalCompletedNativeCorrectedMaterialAtlasCarrier :=
  (0, energy)

@[simp] theorem canonicalCompletedNativeCorrectedMaterialAtlasRadialInjection_fst
    (energy : NativeGpreTowerHilbert) :
    (canonicalCompletedNativeCorrectedMaterialAtlasRadialInjection energy).1 = 0 :=
  rfl

@[simp] theorem canonicalCompletedNativeCorrectedMaterialAtlasRadialInjection_snd
    (energy : NativeGpreTowerHilbert) :
    (canonicalCompletedNativeCorrectedMaterialAtlasRadialInjection energy).2 = energy :=
  rfl

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

theorem canonicalCompletedNativeCorrectedMaterialAtlasState_eq_radialInjection
    (M : ℕ) (s : ℂ) :
    canonicalCompletedNativeCorrectedMaterialAtlasState M s =
      canonicalCompletedNativeCorrectedMaterialAtlasRadialInjection
        (nativeGpreGreenEnergyFirstLevelState (3 * M) s) := by
  rw [canonicalCompletedNativeCorrectedMaterialAtlasState_eq_sameEdge]
  rfl

theorem nativeGpreReflectedFirstLevelGapProfile_eq_zero_of_critical
    (p : Nat.Primes) {s : ℂ}
    (hcritical : criticalDisplacement s.re = 0) :
    nativeGpreReflectedFirstLevelGapProfile p s = 0 := by
  have hsre : s.re = (1 : ℝ) / 2 := by
    unfold criticalDisplacement at hcritical
    linarith
  have hexponent : (2⁻¹ : ℝ) - 1 = -(2⁻¹ : ℝ) := by
    norm_num
  simp [nativeGpreReflectedFirstLevelGapProfile,
    nativeGpreRealTimeFirstLevelProfile, hsre, hexponent]

def canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout
    (p : Nat.Primes) (s : ℂ) (energy : NativeGpreTowerHilbert) : ℝ × ℝ :=
  nativeGpreTfvdCompletedPrecompressionPrimeReadout p s
    (canonicalCompletedNativeCorrectedMaterialAtlasRadialInjection energy)

theorem canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout_eq_components
    (p : Nat.Primes) (s : ℂ) (energy : NativeGpreTowerHilbert) :
    canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout p s energy =
      (0, inner ℝ (nativeGpreReflectedFirstLevelGapProfile p s) energy) := by
  simp [canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout,
    canonicalCompletedNativeCorrectedMaterialAtlasRadialInjection,
    nativeGpreTfvdCompletedPrecompressionPrimeReadout]

theorem canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout_eq_zero_of_critical
    (p : Nat.Primes) (s : ℂ) (energy : NativeGpreTowerHilbert)
    (hcritical : criticalDisplacement s.re = 0) :
    canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout p s energy = 0 := by
  rw [canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout_eq_components,
    nativeGpreReflectedFirstLevelGapProfile_eq_zero_of_critical p hcritical]
  simp

theorem canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout_eq_greenBulk
    (M : ℕ) (s : ℂ) (p : Nat.Primes) :
      canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout p s
        (nativeGpreGreenEnergyFirstLevelState (3 * M) s) =
      (0, primeCarryGreenBulkCutoffProfile (3 * M) s p) := by
  unfold canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout
    canonicalCompletedNativeCorrectedMaterialAtlasRadialInjection
    nativeGpreTfvdCompletedPrecompressionPrimeReadout
  simp only [inner_zero_right]
  exact congrArg (fun x : ℝ => (0, x))
    (inner_nativeGpreReflectedFirstLevelGapProfile_eq_greenBulk
      (3 * M) s p)

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

/-! ## Corrected material-to-`G_pre` crosswalk

The corrected radial readout now meets the provenance-preserving commutator
prefix at the scalar boundary. This is a camera-by-camera, pre-Hankel
crosswalk; `tau` remains explicit and no common fixed-time source is claimed.
-/

theorem canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout_eq_prefixSourceMoment
    (p : Nat.Primes) (tau M : ℕ) (s : ℂ) :
    canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout p s
        (nativeGpreGreenEnergyFirstLevelState (3 * M) s) =
      (0, inner ℝ (nativeGpreTowerProfileVector (p : ℕ) tau)
        (canonicalCompletedNativeCorrectedMaterialAtlasPrefixSource p tau M s)) := by
  rw [canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout_eq_greenBulk]
  exact congrArg (fun x : ℝ => (0, x))
    ((inner_canonicalCompletedNativeCorrectedMaterialAtlasPrefixSource_eq_greenBulk
      p tau M s).trans (finiteNativeGpreLogJetGreenBulkReadout_eq p M s)).symm

/-! ## Corrected material to native four-corner flux

The next seam is still below Hankel/Jacobi.  The corrected material readout
is the radial prime coefficient applied to the actual four-corner `G_pre`
prefix energy, and the same scalar is the normalized log-jet wedge readout.
These are two exact views of the same finite native synthesis.
-/

theorem canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout_eq_fourCornerPrefix
    (p : Nat.Primes) (M : ℕ) (s : ℂ) :
    canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout p s
        (nativeGpreGreenEnergyFirstLevelState (3 * M) s) =
      (0, primeCarryGreenRadialProfile (criticalDisplacement s.re) p *
        (nativeGpreFourCornerDirichletPrefixReadout (3 * M) s).re) := by
  rw [canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout_eq_greenBulk,
    primeCarryGreenBulkCutoffProfile_eq,
    nativeGpreFourCornerDirichletPrefixReadout_eq_pairing]

theorem canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout_eq_normalizedLogJetReadout
    (p : Nat.Primes) (M : ℕ) (s : ℂ) :
    canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout p s
        (nativeGpreGreenEnergyFirstLevelState (3 * M) s) =
      (0, finiteNativeGpreLogJetGreenBulkReadout p M s) := by
  rw [canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout_eq_greenBulk,
    finiteNativeGpreLogJetGreenBulkReadout_eq]

theorem canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout_eq_normalizedLogJetWedge
    (p : Nat.Primes) (M : ℕ) (s : ℂ) :
    canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout p s
        (nativeGpreGreenEnergyFirstLevelState (3 * M) s) =
      (0,
        (((-(((primeCarryAmplitudeRatio p : ℝ) : ℂ) /
          ((Real.log (p : ℝ) : ℝ) : ℂ))) *
          finiteCanonicalCpLogJetCommutatorWedgeTrace
            (p : ℕ) M s).re)) := by
  rw [canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout_eq_normalizedLogJetReadout]
  rfl

theorem canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout_eq_normalizedOrientedGreenFlux
    (p : Nat.Primes) (M : ℕ) (s : ℂ) :
    canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout p s
        (nativeGpreGreenEnergyFirstLevelState (3 * M) s) =
      (0,
        (((primeCarryAmplitudeRatio p : ℝ) : ℂ) *
          finiteOrientedCpGreenFlux (p : ℕ) (3 * M) s).re) := by
  rw [canonicalCompletedNativeCorrectedMaterialAtlasRadialTransportReadout_eq_normalizedLogJetWedge]
  congr 1
  exact congrArg Complex.re
    (finiteNativeGpreLogJetGreenBulkReadout_complex_eq p M s)

/-! ## Finite and completed Wronskian sewing on the same carrier

The four-corner prefix above is not merely a scalar energy readout.  It is
the native carrier already used by the mixed TFVD/Green ledger.  Exposing the
ledger equation here gives the exact finite sewing gate and its completed
limit without identifying a prime readout directly with a Taylor coefficient.
-/

theorem canonicalCompletedNativeCorrectedMaterialAtlas_fourCornerWronskianSewing_iff_totalDefect_zero
    (M : ℕ) {z w : ℂ} (hz : -1 < z.re) (hw : -1 < w.re) :
    canonicalCompletedC3RawMixedWronskian z w =
        canonicalC3MixedRadialCoefficient z w *
          nativeGpreFourCornerPolarizedDirichletPrefix
            (3 * M) w (reflectedParameter z) ↔
      canonicalC3FiniteMixedTotalDefect M z w = 0 := by
  rw [canonicalCompletedC3RawMixedWronskian_eq_nativeFourCorner_add_totalDefect
    M hz hw]
  constructor
  · intro h
    linear_combination h
  · intro h
    rw [h]
    ring

theorem canonicalCompletedNativeCorrectedMaterialAtlas_completedWronskianSewing_iff_defect_limit_zero
    {z w : ℂ} (hz : 0 < z.re) (hzUpper : z.re < 1)
    (hw : 0 < w.re) :
    canonicalCompletedC3RawMixedWronskian z w =
        canonicalC3MixedRadialCoefficient z w *
          canonicalCompletedC3RawGammaGram
            w (reflectedParameter z) hw
            (by simpa [reflectedParameter] using sub_pos.mpr hzUpper) ↔
      Tendsto
        (fun M : ℕ =>
          canonicalNativePolarizedTfvdGreenMomentKernelDefect M z w)
        atTop (nhds 0) := by
  exact canonicalNativePolarizedTfvdGreenMomentKernel_eq_nativeFourCorner_iff_defect_limit_zero
    hz hzUpper hw

/-! ## Native cancellation at the completed seam

The independent completion tail is already an exact vanishing channel.  Thus
the limit of the total native sewing defect is zero exactly when the retained
finite structural defect is zero in the limit.  This is the cancellation that
can be used before transporting any boundary coefficient; it does not identify
the material clock's first column by itself.
-/

theorem canonicalCompletedNativeCorrectedMaterialAtlas_totalDefect_tendsto_zero_iff_structuralDefect_tendsto_zero
    {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    Tendsto
        (fun M : ℕ => canonicalC3FiniteMixedTotalDefect M z w)
        atTop (nhds 0) ↔
      Tendsto
        (fun M : ℕ => canonicalC3FiniteMixedStructuralDefect M z w)
        atTop (nhds 0) := by
  have htail := canonicalC3MixedTailCompletionDefect_tendsto_zero
    (z := z) (w := w) hz hw
  constructor
  · intro htotal
    have hsub := htotal.sub htail
    simpa [canonicalC3FiniteMixedTotalDefect, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm] using hsub
  · intro hstructural
    have hadd := hstructural.add htail
    simpa [canonicalC3FiniteMixedTotalDefect, add_assoc, add_left_comm,
      add_comm] using hadd

/-! ## Height specialization of the native no-leak cancellation

The completed height defect has a sharper native criterion: at a Genuine zero
it disappears exactly on the critical line.  We expose that criterion in the
corrected-material module so it can be consumed by the later boundary and
height gates without reintroducing a fitted positive carrier.
-/

theorem canonicalCompletedNativeCorrectedMaterialAtlas_heightStructuralDefect_tendsto_zero_iff_critical
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
        (fun M : ℕ => canonicalC3FiniteMixedHeightStructuralDefect M s s)
        atTop (nhds 0) ↔
      s.re = (1 : ℝ) / 2 := by
  exact canonicalC3FiniteMixedHeightStructuralDefect_tendsto_zero_at_genuineZero_iff
    hs hzero

theorem canonicalCompletedNativeCorrectedMaterialAtlas_heightStructuralDefect_tendsto_zero_of_critical
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hcritical : s.re = (1 : ℝ) / 2) :
    Tendsto
        (fun M : ℕ => canonicalC3FiniteMixedHeightStructuralDefect M s s)
        atTop (nhds 0) := by
  exact
    (canonicalCompletedNativeCorrectedMaterialAtlas_heightStructuralDefect_tendsto_zero_iff_critical
      hs hzero).2 hcritical

theorem canonicalCompletedNativeCorrectedMaterialAtlas_heightStructuralDefect_not_tendsto_zero_of_offCritical
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    ¬ Tendsto
        (fun M : ℕ => canonicalC3FiniteMixedHeightStructuralDefect M s s)
        atTop (nhds 0) := by
  exact canonicalC3FiniteMixedHeightStructuralDefect_not_tendsto_zero_of_offCritical_genuineZero
    hs hzero hoff

theorem canonicalCompletedNativeCorrectedMaterialAtlas_heightNoLeak_iff_reflectedGapFixedTimeMomentState
    (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    CanonicalC3StructuralNoLeakAt s ↔
      NativeGpreReflectedGapHasFixedTimeMomentStateAt (3 * N) s := by
  exact canonicalC3StructuralNoLeakAt_iff_reflectedGapFixedTimeMomentState
    N hN hs hzero

/-! ## The native boundary target before material-clock transport

The corrected chiral coefficient is not merely named by the response.  The
expanded native structural carrier realizes the same coefficient after the
four structural channels (head, exact tail, xi completion, and chart
correction) have been synthesized inside each chiral sector.  This keeps the
native target concrete and still strictly pre-Hankel.
-/

theorem canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_expandedStructuralSignature
    (M p q : ℕ) :
    canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M (p + q) =
      canonicalCompletedC3ExpandedStructuralSignatureTaylorCoefficient
        M (p + q + 1) := by
  rw [canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_polarizedMoment,
    canonicalCompletedC3ExpandedStructuralSignature_succ_eq_polarizedMoment]

theorem canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_zero_eq_expandedStructuralFirstVariation
    (M : ℕ) :
    canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M 0 =
      canonicalCompletedC3ExpandedStructuralSignatureTaylorCoefficient M 1 := by
  simpa using
    canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_expandedStructuralSignature
      M 0 0

/-! The remaining material handoff can therefore be stated directly against
the explicit native structural synthesis.  This is an equivalence, not a
calibration theorem: it exposes exactly what a genuine material atlas must
prove. -/

theorem hasCorrectedNativeChiralBoundaryTransport_iff_expandedStructuralSignature
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock) :
    HasCorrectedNativeChiralBoundaryTransport M block ↔
      ∀ p : ℕ,
        seededClockAtlasCoefficient block p 0 =
          canonicalCompletedC3ExpandedStructuralSignatureTaylorCoefficient
            M (p + 1) := by
  constructor
  · intro h p
    calc
      seededClockAtlasCoefficient block p 0 =
          canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p :=
        h p
      _ = canonicalCompletedC3ExpandedStructuralSignatureTaylorCoefficient
          M (p + 1) := by
        simpa using
          canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_expandedStructuralSignature
            M p 0
  · intro h p
    calc
      seededClockAtlasCoefficient block p 0 =
          canonicalCompletedC3ExpandedStructuralSignatureTaylorCoefficient
            M (p + 1) := h p
      _ = canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p := by
        simpa using
          (canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_expandedStructuralSignature
            M p 0).symm

end

end CarrySelfAdjointOperator
