import CarrySelfAdjointOperator.CompletedNativeDirichletChiralCrossLedger
import CarrySelfAdjointOperator.CompletedC3ChiralCrossedChartBridge
import Mathlib.Tactic

/-!
# Completed native chiral energy ledger

The finite C3 height ledger consists of positive local Dirichlet energy and
ordered cross-frequency provenance.  This module applies the exact product
rule used by the completed characteristic: the raw ledger is weighted by the
xi factor and the independently retained archimedean/chart mixed channel is
added without scalar collapse.

The resulting finite ledger converges exactly to the completed full chiral
balance.  No sign, zero-set, Stieltjes, Jacobi, or confinement hypothesis is
introduced.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- A diagonal Hermitian scalar weight is the real squared modulus of its
underlying scalar channel. -/
theorem mixedHermitianWeight_self_eq_normSq
    (H : ℂ → ℂ) (z : ℂ) :
    mixedHermitianWeight H z z = (Complex.normSq (H z) : ℂ) := by
  unfold mixedHermitianWeight
  rw [Complex.mul_conj]

/-- Finite raw height wedge at the centered parameter attached to `z`. -/
def canonicalC3FiniteRawHeightBoundaryWedge (M : ℕ) (z : ℂ) : ℂ :=
  scalarBoundaryWedge
    (finiteBracketedDirichletChart 3 M (operatorHeightParameter z))
    (Complex.I *
      finiteCanonicalLogBracketChart M (operatorHeightParameter z))

/-- Finite completed numerator: xi-weighted raw C3 height ledger plus the
exact archimedean/chart product channel. -/
def canonicalC3FiniteCompletedChiralEnergyLedger
    (M : ℕ) (z : ℂ) : ℝ :=
  (mixedHermitianWeight nativeXiCompletionFactor z z *
      canonicalC3FiniteRawHeightBoundaryWedge M z +
    canonicalCompletedC3ArchimedeanChartMixedChannel z z).im

/-- Positive local component of the finite completed ledger. -/
def canonicalC3FiniteCompletedPositiveLocalEnergy
    (M : ℕ) (z : ℂ) : ℝ :=
  Complex.normSq (nativeXiCompletionFactor z) *
    canonicalC3FiniteDirichletLocalHeightEnergy M
      (operatorHeightParameter z)

/-- Complete nonlocal component retained beside the positive local energy:
xi-weighted cross provenance plus the archimedean/chart channel. -/
def canonicalC3FiniteCompletedCrossArchChannel
    (M : ℕ) (z : ℂ) : ℝ :=
  Complex.normSq (nativeXiCompletionFactor z) *
      (scalarBoundaryCrossProvenance
        (canonicalC3FiniteDirichletValueAtom M (operatorHeightParameter z))
        (canonicalC3FiniteDirichletHeightCompanionAtom M
          (operatorHeightParameter z))).im +
    (canonicalCompletedC3ArchimedeanChartMixedChannel z z).im

/-- The completed finite ledger splits exactly into its positive local
component and the retained cross-plus-archimedean channel. -/
theorem canonicalC3FiniteCompletedChiralEnergyLedger_eq_local_add_crossArch
    (M : ℕ) (z : ℂ) :
    canonicalC3FiniteCompletedChiralEnergyLedger M z =
      canonicalC3FiniteCompletedPositiveLocalEnergy M z +
        canonicalC3FiniteCompletedCrossArchChannel M z := by
  unfold canonicalC3FiniteCompletedChiralEnergyLedger
    canonicalC3FiniteRawHeightBoundaryWedge
    canonicalC3FiniteCompletedPositiveLocalEnergy
    canonicalC3FiniteCompletedCrossArchChannel
  rw [mixedHermitianWeight_self_eq_normSq]
  rw [Complex.add_im, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  rw [finiteC3HeightBoundaryWedge_im_eq_localEnergy_add_crossProvenance]
  ring

/-- The completed local component remains nonnegative after the exact xi
weight is restored. -/
theorem canonicalC3FiniteCompletedPositiveLocalEnergy_nonneg
    (M : ℕ) (z : ℂ) :
    0 ≤ canonicalC3FiniteCompletedPositiveLocalEnergy M z := by
  unfold canonicalC3FiniteCompletedPositiveLocalEnergy
  exact mul_nonneg (Complex.normSq_nonneg _)
    (canonicalC3FiniteDirichletLocalHeightEnergy_nonneg M
      (operatorHeightParameter z))

/-- Exact finite completed sign gate: the nonlocal cross-plus-archimedean
channel may not outweigh the positive local energy. -/
theorem
    canonicalC3FiniteCompletedChiralEnergyLedger_nonneg_iff_crossArch_le_local
    (M : ℕ) (z : ℂ) :
    0 ≤ canonicalC3FiniteCompletedChiralEnergyLedger M z ↔
      -canonicalC3FiniteCompletedCrossArchChannel M z ≤
        canonicalC3FiniteCompletedPositiveLocalEnergy M z := by
  rw [canonicalC3FiniteCompletedChiralEnergyLedger_eq_local_add_crossArch]
  constructor <;> intro h <;> linarith

/-- The complex finite raw wedge converges to the diagonal raw C3
Wronskian. -/
theorem canonicalC3FiniteRawHeightBoundaryWedge_tendsto_rawWronskian
    {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    Filter.Tendsto
      (fun M : ℕ => canonicalC3FiniteRawHeightBoundaryWedge M z)
      Filter.atTop
      (nhds (canonicalCompletedC3RawHeightMixedWronskian z z)) := by
  have hvalue := finiteBracketedDirichletChart_tendsto
    3 (by norm_num) (s := operatorHeightParameter z) (by linarith [hz.1])
  have hlogJet := finiteCanonicalLogBracketChart_tendsto_completed hz.1
  have hheightLogJet := hlogJet.const_mul Complex.I
  have hwedge := scalarBoundaryWedge_tendsto hvalue hheightLogJet
  unfold canonicalC3FiniteRawHeightBoundaryWedge
  rw [canonicalCompletedC3RawHeightMixedWronskian_self_eq_scalarBoundaryWedge]
  rw [canonicalCompletedC3RawHeightValue_eq_bracketedDirichletChart hz]
  exact hwedge

/-- The finite completed ledger converges to the diagonal crossed product
numerator already present in the full Wronskian construction. -/
theorem canonicalC3FiniteCompletedChiralEnergyLedger_tendsto_crossedNumerator
    {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    Filter.Tendsto
      (fun M : ℕ => canonicalC3FiniteCompletedChiralEnergyLedger M z)
      Filter.atTop
      (nhds
        (mixedHermitianWeight nativeXiCompletionFactor z z *
            canonicalCompletedC3RawHeightMixedWronskian z z +
          canonicalCompletedC3ArchimedeanChartMixedChannel z z).im) := by
  have hraw := canonicalC3FiniteRawHeightBoundaryWedge_tendsto_rawWronskian hz
  have hweight : Filter.Tendsto
      (fun _ : ℕ => mixedHermitianWeight nativeXiCompletionFactor z z)
      Filter.atTop
      (nhds (mixedHermitianWeight nativeXiCompletionFactor z z)) :=
    tendsto_const_nhds
  have harch : Filter.Tendsto
      (fun _ : ℕ => canonicalCompletedC3ArchimedeanChartMixedChannel z z)
      Filter.atTop
      (nhds (canonicalCompletedC3ArchimedeanChartMixedChannel z z)) :=
    tendsto_const_nhds
  have hcomplex := (hweight.mul hraw).add harch
  unfold canonicalC3FiniteCompletedChiralEnergyLedger
  exact Complex.continuous_im.continuousAt.tendsto.comp hcomplex

/-- Final completion square: for every fixed full-carrier cutoff, the finite
native ledger converges exactly to the completed signed chiral balance. -/
theorem canonicalC3FiniteCompletedChiralEnergyLedger_tendsto_fullChiralBalance
    (carrierCutoff : ℕ) {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    Filter.Tendsto
      (fun M : ℕ => canonicalC3FiniteCompletedChiralEnergyLedger M z)
      Filter.atTop
      (nhds
        (mixedHermitianWeight canonicalC3ChartFactorHeight z z *
            canonicalCompletedC3GammaCharacteristicWeight z z *
            (Complex.I *
              (canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
                  carrierCutoff z z -
                canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
                  carrierCutoff z z))).im) := by
  rw [canonicalCompletedC3FullChiralBalance_crossedChartIdentity
    carrierCutoff hz hz hF hF]
  exact canonicalC3FiniteCompletedChiralEnergyLedger_tendsto_crossedNumerator hz

end

end CarrySelfAdjointOperator
