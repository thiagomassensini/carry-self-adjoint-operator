import CarrySelfAdjointOperator.BR2GreenFrameDslopeLimitBridge
import CarrySelfAdjointOperator.CompletedNativeProjectiveChiralCarrier
import Mathlib.Tactic

/-!
# Source Parseval / projective-chiral Cauchy--Pick sewing

Unconditional preservation of the two-arm source form; finite-coefficient
contractivity; and an explicit metric-sewing defect against the existing
canonical radial projective-chiral carrier. No missing physical-to-Cauchy
operator is assumed or constructed, and no positivity is presupposed.
-/

namespace CarrySelfAdjointOperator

open scoped InnerProductSpace ComplexConjugate ComplexOrder MatrixOrder
noncomputable section

def sourceChiralSignedPairing
    (v w : CPFormal.Analytic.Cp.CarryVerticalL2 × CPFormal.Analytic.Cp.CarryVerticalL2) : ℂ :=
  (2 : ℂ)⁻¹ * (inner ℂ v.1 w.1 - inner ℂ v.2 w.2)

def sourceChiralParsevalPairing
    (v w : CPFormal.Analytic.Cp.CarryVerticalL2 × CPFormal.Analytic.Cp.CarryVerticalL2) : ℂ :=
  (2 : ℂ)⁻¹ *
    (inner ℂ
        (canonicalCompletedGreenFrameParsevalAnalysis v.1)
        (canonicalCompletedGreenFrameParsevalAnalysis w.1) -
      inner ℂ
        (canonicalCompletedGreenFrameParsevalAnalysis v.2)
        (canonicalCompletedGreenFrameParsevalAnalysis w.2))

theorem sourceChiralParsevalPairing_eq_source
    (v w : CPFormal.Analytic.Cp.CarryVerticalL2 × CPFormal.Analytic.Cp.CarryVerticalL2) :
    sourceChiralParsevalPairing v w = sourceChiralSignedPairing v w := by
  unfold sourceChiralParsevalPairing sourceChiralSignedPairing
  rw [canonicalCompletedGreenFrameParsevalAnalysis_inner,
      canonicalCompletedGreenFrameParsevalAnalysis_inner]

def sourceChiralParsevalDefectMatrix (N : ℕ)
    (incident outgoing : Fin N → CPFormal.Analytic.Cp.CarryVerticalL2) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.gram ℂ (fun i => canonicalCompletedGreenFrameParsevalAnalysis (incident i)) -
    Matrix.gram ℂ (fun i => canonicalCompletedGreenFrameParsevalAnalysis (outgoing i))

theorem sourceChiralParsevalDefectMatrix_eq_source (N : ℕ)
    (incident outgoing : Fin N → CPFormal.Analytic.Cp.CarryVerticalL2) :
    sourceChiralParsevalDefectMatrix N incident outgoing =
      Matrix.gram ℂ incident - Matrix.gram ℂ outgoing := by
  ext i j
  simp only [sourceChiralParsevalDefectMatrix, Matrix.sub_apply, Matrix.gram_apply]
  rw [canonicalCompletedGreenFrameParsevalAnalysis_inner,
      canonicalCompletedGreenFrameParsevalAnalysis_inner]

/-- A genuine sign gate: simultaneous finite-combination domination,
rather than pointwise positivity of the two arms. -/
theorem sourceChiralParsevalDefectMatrix_posSemidef_iff (N : ℕ)
    (incident outgoing : Fin N → CPFormal.Analytic.Cp.CarryVerticalL2) :
    (sourceChiralParsevalDefectMatrix N incident outgoing).PosSemidef ↔
      ∀ c : Fin N → ℂ,
        ‖∑ i, c i • outgoing i‖ ≤ ‖∑ i, c i • incident i‖ := by
  rw [sourceChiralParsevalDefectMatrix_eq_source]
  exact gram_sub_gram_posSemidef_iff_synthesis_norm_le incident outgoing

def sourceProjectiveChiralMetricSewingDefect (k N : ℕ)
    (incident outgoing : Fin N → CPFormal.Analytic.Cp.CarryVerticalL2)
    (i j : Fin N) : ℂ :=
  sourceChiralParsevalPairing
      (incident i, outgoing i) (incident j, outgoing j) -
    canonicalCompletedNativeRadialDslopeSampleMatrix k N i j

def sourceProjectiveChiralPositiveMismatch (k N : ℕ)
    (incident : Fin N → CPFormal.Analytic.Cp.CarryVerticalL2) (i j : Fin N) : ℂ :=
  inner ℂ (incident i) (incident j) -
    inner ℂ
      (canonicalCompletedNativeRadialProjectiveChiralState k i).1
      (canonicalCompletedNativeRadialProjectiveChiralState k j).1

def sourceProjectiveChiralNegativeMismatch (k N : ℕ)
    (outgoing : Fin N → CPFormal.Analytic.Cp.CarryVerticalL2) (i j : Fin N) : ℂ :=
  inner ℂ (outgoing i) (outgoing j) -
    inner ℂ
      (canonicalCompletedNativeRadialProjectiveChiralState k i).2
      (canonicalCompletedNativeRadialProjectiveChiralState k j).2

/-- Exact oriented residual: complete physical plus-channel mismatch
minus complete physical minus-channel mismatch. -/
theorem sourceProjectiveChiralMetricSewingDefect_eq_mismatches
    (k N : ℕ)
    (hregular : ∀ i : Fin N,
      canonicalCompletedC3RadialTiltPoint k i ∈ completedNativeHeightDomain ∧
      completedNativeOperatorCharacteristic
        (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate
        (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (incident outgoing : Fin N → CPFormal.Analytic.Cp.CarryVerticalL2) (i j : Fin N) :
    sourceProjectiveChiralMetricSewingDefect k N incident outgoing i j =
      (2 : ℂ)⁻¹ *
        (sourceProjectiveChiralPositiveMismatch k N incident i j -
         sourceProjectiveChiralNegativeMismatch k N outgoing i j) := by
  rw [sourceProjectiveChiralMetricSewingDefect,
      sourceChiralParsevalPairing_eq_source,
      ← canonicalCompletedNativeRadialProjectiveChiralSampleMatrix_eq_dslope k N hregular]
  simp only [sourceChiralSignedPairing,
    canonicalCompletedNativeRadialProjectiveChiralSampleMatrix, Matrix.of_apply,
    canonicalCompletedNativeProjectiveChiralForm,
    sourceProjectiveChiralPositiveMismatch, sourceProjectiveChiralNegativeMismatch]
  ring

/-- Target realization is equivalent to cancellation of the two full
source/channel mismatches; no cancellation is assumed. -/
theorem sourceProjectiveChiralMetricSewingDefect_zero_iff
    (k N : ℕ)
    (hregular : ∀ i : Fin N,
      canonicalCompletedC3RadialTiltPoint k i ∈ completedNativeHeightDomain ∧
      completedNativeOperatorCharacteristic
        (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate
        (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (incident outgoing : Fin N → CPFormal.Analytic.Cp.CarryVerticalL2) :
    (∀ i j : Fin N,
      sourceProjectiveChiralMetricSewingDefect k N incident outgoing i j = 0) ↔
    (∀ i j : Fin N,
      sourceProjectiveChiralPositiveMismatch k N incident i j =
      sourceProjectiveChiralNegativeMismatch k N outgoing i j) := by
  simp_rw [sourceProjectiveChiralMetricSewingDefect_eq_mismatches k N hregular]
  simp only [mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or,
    sub_eq_zero]


/-- A complete metric sewing makes the canonical radial divided-slope matrix
exactly one half of the transported source defect matrix. In particular, the
proof does not identify either source arm with the Cauchy arm individually. -/
theorem sourceProjectiveChiralDslope_eq_half_sourceDefect
    (k N : ℕ)
    (incident outgoing : Fin N → CPFormal.Analytic.Cp.CarryVerticalL2)
    (hsewing : ∀ i j : Fin N,
      sourceProjectiveChiralMetricSewingDefect k N incident outgoing i j = 0) :
    canonicalCompletedNativeRadialDslopeSampleMatrix k N =
      (2 : ℝ)⁻¹ • sourceChiralParsevalDefectMatrix N incident outgoing := by
  ext i j
  have h := hsewing i j
  unfold sourceProjectiveChiralMetricSewingDefect at h
  have hp : sourceChiralParsevalPairing
      (incident i, outgoing i) (incident j, outgoing j) =
      canonicalCompletedNativeRadialDslopeSampleMatrix k N i j :=
    sub_eq_zero.mp h
  rw [← hp]
  simp only [sourceChiralParsevalPairing, sourceChiralParsevalDefectMatrix,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.gram_apply,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_ofNat]

/-- The actual physical source domination gives the canonical matrix sign
ONLY after a complete all-crosses metric sewing. Both inputs remain explicit
and source-first; no target positivity or abstract moment representation is
assumed as an input. -/
theorem sourceProjectiveChiralDslope_posSemidef_of_sewing_and_contractivity
    (k N : ℕ)
    (incident outgoing : Fin N → CPFormal.Analytic.Cp.CarryVerticalL2)
    (hsewing : ∀ i j : Fin N,
      sourceProjectiveChiralMetricSewingDefect k N incident outgoing i j = 0)
    (hcontractive : ∀ c : Fin N → ℂ,
      ‖∑ i, c i • outgoing i‖ ≤ ‖∑ i, c i • incident i‖) :
    (canonicalCompletedNativeRadialDslopeSampleMatrix k N).PosSemidef := by
  rw [sourceProjectiveChiralDslope_eq_half_sourceDefect k N
    incident outgoing hsewing]
  exact ((sourceChiralParsevalDefectMatrix_posSemidef_iff
    N incident outgoing).mpr hcontractive).smul (by norm_num)

end
end CarrySelfAdjointOperator

/-! Dependency audit of the source-side and canonical-target seam. -/
#print axioms CarrySelfAdjointOperator.sourceChiralParsevalPairing_eq_source
#print axioms CarrySelfAdjointOperator.sourceChiralParsevalDefectMatrix_eq_source
#print axioms CarrySelfAdjointOperator.sourceChiralParsevalDefectMatrix_posSemidef_iff
#print axioms CarrySelfAdjointOperator.sourceProjectiveChiralMetricSewingDefect_eq_mismatches
#print axioms CarrySelfAdjointOperator.sourceProjectiveChiralMetricSewingDefect_zero_iff
#print axioms CarrySelfAdjointOperator.sourceProjectiveChiralDslope_eq_half_sourceDefect
#print axioms CarrySelfAdjointOperator.sourceProjectiveChiralDslope_posSemidef_of_sewing_and_contractivity
