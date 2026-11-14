import CarrySelfAdjointOperator.C2LegCauchySynthesis
import CarrySelfAdjointOperator.C2LegCompletionPolarization
import CarrySelfAdjointOperator.CompletedNativeChiralReturnSourceTrace
import CarrySelfAdjointOperator.CompletedNativeChiralReturnGammaCorrectionCancellation
import CarrySelfAdjointOperator.CompletedNativeSemidefiniteHardyGate

/-!
# Transport finite C2 legs in the original completed Cauchy carrier

The approximants below retain the complete-source chiral denominator and
the original radial Cauchy states. The finite D central/leg companions are
synthesized in that same carrier. No Gamma-to-central equality or tail
convergence is assumed.
-/

namespace CarrySelfAdjointOperator

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open ChiralReturn CPFormal.Analytic.Cp

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Original source coefficient at a radial Cauchy node, with the complete
source Hermite--Biehler denominator retained in every finite approximation. -/
def nativeSourceC2SourceWeight (n k : ℕ) (x : Fin (2*n) → ℂ)
    (i : Fin (2*n)) : ℂ :=
  nativeSourceChiralJetInput n k x i /
    completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i)

/-- Finite C2 value synthesis at the original source nodes. -/
def nativeSourceC2ApproxValue (n k M : ℕ) (x : Fin (2*n) → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  c2CauchyValueSynthesis (nativeSourceC2SourceWeight n k x)
    (fun i => c2FiniteChartHeightCharacteristic M
      (canonicalCompletedC3RadialTiltPoint k i))
    (fun i => completedNativeRadialChiralCauchyState k i)

/-- Finite central companion synthesis in the original source carrier. -/
def nativeSourceC2ApproxCentral (n k M : ℕ) (x : Fin (2*n) → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  c2CauchyCentralSynthesis (nativeSourceC2SourceWeight n k x)
    (fun i => c2FiniteChartHeightCentralCompanion M
      (canonicalCompletedC3RadialTiltPoint k i))
    (fun i => completedNativeRadialChiralCauchyState k i)

/-- Finite two-leg companion synthesis in the original source carrier. -/
def nativeSourceC2ApproxLegs (n k M : ℕ) (x : Fin (2*n) → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  c2CauchyLegSynthesis (nativeSourceC2SourceWeight n k x)
    (fun i => c2CompletionDressing
      (canonicalCompletedC3RadialTiltPoint k i))
    (fun i => c2FiniteChartHeightLegCorrection M
      (canonicalCompletedC3RadialTiltPoint k i))
    (fun i => completedNativeRadialChiralCauchyState k i)

/-- Full finite C2 companion synthesis, before splitting its central and leg
parts. -/
def nativeSourceC2ApproxCompanion (n k M : ℕ) (x : Fin (2*n) → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  c2CauchyCompanionSynthesis (nativeSourceC2SourceWeight n k x)
    (fun i => c2FiniteChartHeightCompanion M
      (canonicalCompletedC3RadialTiltPoint k i))
    (fun i => completedNativeRadialChiralCauchyState k i)

/-- The finite value tail is a declared vector difference; no convergence is
asserted. -/
def nativeSourceC2ValueTail (n k M : ℕ) (x : Fin (2*n) → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  sourceValue k (nativeSourceChiralJetInput n k x) 1 -
    nativeSourceC2ApproxValue n k M x

/-- The finite companion tail is a declared vector difference; no convergence
is asserted. -/
def nativeSourceC2CompanionTail (n k M : ℕ) (x : Fin (2*n) → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  sourceCompanion k (nativeSourceChiralJetInput n k x) 1 -
    nativeSourceC2ApproxCompanion n k M x

/-- Explicit E2 tail budget for the original complete and finite C2 vectors. -/
def nativeSourceC2TailError (n k M : ℕ) (x : Fin (2*n) → ℂ) : ℝ :=
  2 * (‖nativeSourceC2ValueTail n k M x‖ *
        ‖nativeSourceC2ApproxCompanion n k M x‖ +
      ‖nativeSourceC2ApproxValue n k M x‖ *
        ‖nativeSourceC2CompanionTail n k M x‖ +
      ‖nativeSourceC2ValueTail n k M x‖ *
        ‖nativeSourceC2CompanionTail n k M x‖)

/-- Central-plus-legs finite readout. Its two terms are summed before any
sign estimate; their individual signs are unrestricted. -/
def nativeSourceC2CentralLegReadout (n k M : ℕ)
    (x : Fin (2*n) → ℂ) : ℝ :=
  (inner ℂ (nativeSourceC2ApproxValue n k M x)
    (nativeSourceC2ApproxCentral n k M x)).im +
  (inner ℂ (nativeSourceC2ApproxValue n k M x)
    (nativeSourceC2ApproxLegs n k M x)).re

/-- At radius one, the complete source value is the source-weighted synthesis
of the original characteristic in the original Cauchy carrier. -/
theorem sourceValue_one_eq_nativeSourceC2SourceSynthesis
    (n k : ℕ) (x : Fin (2*n) → ℂ) :
    sourceValue k (nativeSourceChiralJetInput n k x) 1 =
      c2CauchyValueSynthesis (nativeSourceC2SourceWeight n k x)
        (fun i => completedNativeOperatorCharacteristic
          (canonicalCompletedC3RadialTiltPoint k i))
        (fun i => completedNativeRadialChiralCauchyState k i) := by
  unfold ChiralReturn.sourceValue c2CauchyValueSynthesis c2CauchySynthesis
    nativeSourceC2SourceWeight
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  norm_num
  ring

/-- The existing finite D companion identity gives the exact central-plus-leg
decomposition after synthesis, with the original weights and features. -/
theorem nativeSourceC2ApproxCompanion_eq_central_add_legs
    (n k M : ℕ) (x : Fin (2*n) → ℂ) :
    nativeSourceC2ApproxCompanion n k M x =
      nativeSourceC2ApproxCentral n k M x +
        Complex.I • nativeSourceC2ApproxLegs n k M x := by
  unfold nativeSourceC2ApproxCompanion nativeSourceC2ApproxCentral
    nativeSourceC2ApproxLegs
  apply c2CauchyCompanionSynthesis_eq_central_add_legs
  intro i
  have h := c2FiniteChartHeightCompanion_sub_central_eq_legCorrection M
    (canonicalCompletedC3RadialTiltPoint k i)
  calc
    c2FiniteChartHeightCompanion M
        (canonicalCompletedC3RadialTiltPoint k i) =
        (c2FiniteChartHeightCompanion M
          (canonicalCompletedC3RadialTiltPoint k i) -
          c2FiniteChartHeightCentralCompanion M
            (canonicalCompletedC3RadialTiltPoint k i)) +
          c2FiniteChartHeightCentralCompanion M
            (canonicalCompletedC3RadialTiltPoint k i) := by ring
    _ = c2FiniteChartHeightCentralCompanion M
          (canonicalCompletedC3RadialTiltPoint k i) +
        Complex.I * c2CompletionDressing
          (canonicalCompletedC3RadialTiltPoint k i) *
          c2FiniteChartHeightLegCorrection M
            (canonicalCompletedC3RadialTiltPoint k i) := by
      rw [h]
      ring

/-- The complete source Gamma gap is exactly the signed defect in the
original Cauchy carrier whenever the existing strip and denominator
regularity hypotheses hold. -/
theorem nativeSourceC2CompleteDefect_eq_gammaCorrectionGap
    (n k M : ℕ) (x : Fin (2*n) → ℂ)
    (hstrip : ∀ i : Fin (2*n), operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (hpositive : ∀ i : Fin (2*n), completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    c2CarrierDefect (sourceValue k (nativeSourceChiralJetInput n k x) 1)
      (sourceCompanion k (nativeSourceChiralJetInput n k x) 1) =
        nativeSourceGammaCorrectionGap n k x := by
  simpa [c2CarrierDefect, nativeSourceGammaCorrectionGap] using
    (rawGammaCorrection_energy_gap_eq_source_cross M k
      (nativeSourceChiralJetInput n k x) 1 hstrip hpositive).symm

/-- E2 instantiated in the original source carrier. The entire omitted tail
is explicit, and its size is not assumed to vanish. -/
theorem nativeSourceC2GammaGap_approx_error_bound
    (n k M : ℕ) (x : Fin (2*n) → ℂ)
    (hstrip : ∀ i : Fin (2*n), operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (hpositive : ∀ i : Fin (2*n), completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    |nativeSourceGammaCorrectionGap n k x -
      c2CarrierDefect (nativeSourceC2ApproxValue n k M x)
        (nativeSourceC2ApproxCompanion n k M x)| ≤
      nativeSourceC2TailError n k M x := by
  rw [← nativeSourceC2CompleteDefect_eq_gammaCorrectionGap n k M x
    hstrip hpositive]
  exact c2CarrierDefect_approximation_error_bound
    (sourceValue k (nativeSourceChiralJetInput n k x) 1)
    (sourceCompanion k (nativeSourceChiralJetInput n k x) 1)
    (nativeSourceC2ApproxValue n k M x)
    (nativeSourceC2ApproxCompanion n k M x)

/-- E1 identifies the finite approximate defect as minus twice the sum of
the central and two-leg readouts. -/
theorem nativeSourceC2ApproxDefect_eq_centralLegReadout
    (n k M : ℕ) (x : Fin (2*n) → ℂ) :
    c2CarrierDefect (nativeSourceC2ApproxValue n k M x)
      (nativeSourceC2ApproxCompanion n k M x) =
        -2 * nativeSourceC2CentralLegReadout n k M x := by
  rw [nativeSourceC2ApproxCompanion_eq_central_add_legs]
  simp only [c2CarrierDefect, nativeSourceC2CentralLegReadout]
  rw [inner_add_right, inner_smul_right, Complex.add_im, Complex.I_mul_im]

/-- Exact E4 premise: for each fixed order, a cutoff and two error budgets may
depend on the radial index. The first estimate controls the SUM of central
and leg readouts; the second controls the transported tail. -/
def HasNativeSourceC2LegTailBounds : Prop :=
  ∀ n : ℕ, ∃ M : ℕ → ℕ, ∃ a : ℕ → ℝ, ∃ b : ℕ → ℝ,
    Tendsto a atTop (nhds 0) ∧ Tendsto b atTop (nhds 0) ∧
      ∀ᶠ k : ℕ in atTop, ∀ x : Fin (2*n) → ℂ,
        -a k * ‖x‖^2 ≤ nativeSourceC2CentralLegReadout n k (M k) x ∧
          nativeSourceC2TailError n k (M k) x ≤ b k * ‖x‖^2

/-- E4 turns the summed central/legs estimate and the explicit tail budget
into A's signed Gamma correction envelope. The source estimates remain
explicit hypotheses, and no cutoff/radial limits are interchanged. -/
theorem nativeSourceC2LegTailBounds_imply_gammaCorrectionEnvelope
    (hBounds : HasNativeSourceC2LegTailBounds) :
    HasNativeSourceGammaCorrectionEnvelope := by
  intro n
  rcases hBounds n with ⟨M, a, b, ha, hb, hfinite⟩
  refine ⟨fun k => 2 * a k + b k, ?_, ?_⟩
  · simpa [mul_comm] using (ha.const_mul (2 : ℝ)).add hb
  · filter_upwards [
      canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (2*n),
      hfinite] with k hregular hfinite
    intro x
    rcases hfinite x with ⟨hcentral, htail⟩
    have hstrip : ∀ i : Fin (2*n),
        operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
          genuineCriticalStrip := fun i => (hregular i).1
    have hpositive : ∀ i : Fin (2*n),
        completedNativePositiveHermiteBiehlerCoordinate
          (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 :=
      fun i => (hregular i).2.2
    have herr := nativeSourceC2GammaGap_approx_error_bound n k (M k) x
      hstrip hpositive
    have happrox := nativeSourceC2ApproxDefect_eq_centralLegReadout n k
      (M k) x
    have hgap := (abs_le.mp herr).2
    have happroxUpper :
        c2CarrierDefect (nativeSourceC2ApproxValue n k (M k) x)
          (nativeSourceC2ApproxCompanion n k (M k) x) ≤
          2 * a k * ‖x‖^2 := by
      rw [happrox]
      nlinarith [hcentral]
    calc
      nativeSourceGammaCorrectionGap n k x ≤
          c2CarrierDefect (nativeSourceC2ApproxValue n k (M k) x)
            (nativeSourceC2ApproxCompanion n k (M k) x) +
            b k * ‖x‖^2 := by nlinarith [hgap, htail]
      _ ≤ 2 * a k * ‖x‖^2 + b k * ‖x‖^2 :=
        by nlinarith [happroxUpper]
      _ = (2 * a k + b k) * ‖x‖^2 := by ring

/-- A's strict positivity consumer is applied only with its Hardy hypothesis
still visible; this theorem closes no source estimate by itself. -/
theorem nativeSourceC2LegTailBounds_imply_canonicalHankelPair_posDef
    (hzeros : InfinitePositiveRealNativeZeros)
    (hBounds : HasNativeSourceC2LegTailBounds) :
    (∀ n, (hankelGram canonicalCompletedNativeLogDerivativeMoment n).PosDef) ∧
    (∀ n, (shiftedHankel canonicalCompletedNativeLogDerivativeMoment n).PosDef) := by
  exact canonicalHankelPair_posDef_of_gammaCorrectionEnvelope hzeros
    (nativeSourceC2LegTailBounds_imply_gammaCorrectionEnvelope hBounds)

end
end CarrySelfAdjointOperator
