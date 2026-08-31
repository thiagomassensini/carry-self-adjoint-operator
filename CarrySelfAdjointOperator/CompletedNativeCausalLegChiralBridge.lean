import CarrySelfAdjointOperator.CompletedNativeHermiteBiehlerChiralTrace
import CarrySelfAdjointOperator.CompletedC3GenuineBracketGreenTransport
import CarrySelfAdjointOperator.CompletedEnrichedTfvdBoundaryCompanion
import CarrySelfAdjointOperator.ReflectedScalarBoundaryResidual
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-!
# Causal center--leg reconstruction of the completed chiral trace

The causal cell `left - 2 * center + right` commutes exactly with the
logarithmic derivative.  Consequently the value state and its logarithmic
jet are reconstructed by the same two-seed, all-cell bracket ledger.

This module then places that center--leg identity inside the scalar chiral
boundary readout.  Finite telescoping recovers every local wedge, while the
ordered cross-cell provenance remains explicit.  No positivity or
confinement statement is inserted into that provenance term.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-! ## The logarithmic jet uses the same causal cells -/

/-- Logarithmic value state on the same positive-index ledger as the causal
Dirichlet value state. -/
def canonicalC3CausalLogJetState (s : ℂ) : ℕ → ℂ :=
  positiveLogDirichletValue s

/-- Pointwise, the logarithmic state is exactly minus the parameter
derivative of the value state. -/
theorem hasDerivAt_canonicalC3CausalValueState_eq_neg_logJet
    (s : ℂ) (n : ℕ) :
    HasDerivAt (fun u : ℂ => canonicalC3CausalValueState u n)
      (-canonicalC3CausalLogJetState s n) s := by
  have h := hasDerivAt_natDirichletTerm_eq_neg_natLogDirichletTerm
    (n + 1) (by omega) s
  simpa [canonicalC3CausalValueState, canonicalC3CausalLogJetState,
    positiveDirichletValue_eq_natDirichletTerm,
    positiveLogDirichletValue_eq_natLogDirichletTerm] using h

/-- Differentiation commutes with the complete left--center--right causal
cell, including its orientation and coefficient `2`. -/
theorem hasDerivAt_causalUnitBracket_value_eq_neg_logJet
    (s : ℂ) (left : ℕ) :
    HasDerivAt
      (fun u : ℂ => causalUnitBracket (canonicalC3CausalValueState u) left)
      (-causalUnitBracket (canonicalC3CausalLogJetState s) left) s := by
  have hleft :=
    hasDerivAt_canonicalC3CausalValueState_eq_neg_logJet s left
  have hcenter :=
    hasDerivAt_canonicalC3CausalValueState_eq_neg_logJet s (left + 1)
  have hright :=
    hasDerivAt_canonicalC3CausalValueState_eq_neg_logJet s (left + 2)
  rw [show (fun u : ℂ =>
      causalUnitBracket (canonicalC3CausalValueState u) left) =
      (fun u : ℂ =>
        canonicalC3CausalValueState u left -
          2 * canonicalC3CausalValueState u (left + 1) +
            canonicalC3CausalValueState u (left + 2)) by
    funext u
    simp [causalUnitBracket, nsmul_eq_mul]]
  refine ((hleft.sub (hcenter.const_mul 2)).add hright).congr_deriv ?_
  simp only [causalUnitBracket, nsmul_eq_mul]
  ring

/-- Causal data carried by the logarithmic state. -/
def canonicalC3CausalLogJetBracketData (s : ℂ) : CausalBracketData ℂ :=
  { leftSeed := canonicalC3CausalLogJetState s 0
    centerSeed := canonicalC3CausalLogJetState s 1
    bracket := causalUnitBracket (canonicalC3CausalLogJetState s) }

theorem canonicalC3CausalLogJetState_realizes (s : ℂ) :
    RealizesCausalBracketData
      (canonicalC3CausalLogJetBracketData s)
      (canonicalC3CausalLogJetState s) := by
  exact ⟨rfl, rfl, fun _ => rfl⟩

/-- The same double telescope reconstructs the complete logarithmic state. -/
theorem canonicalC3CausalLogJetReconstruction_eq_state (s : ℂ) :
    causalBracketReconstruction (canonicalC3CausalLogJetBracketData s) =
      canonicalC3CausalLogJetState s := by
  exact (causalBracketReconstruction_unique
    (canonicalC3CausalLogJetBracketData s)
    (canonicalC3CausalLogJetState s)
    (canonicalC3CausalLogJetState_realizes s)).symm

/-- Explicit right-leg reconstruction for the logarithmic state. -/
theorem canonicalC3CausalLogJetState_rightLeg (s : ℂ) (left : ℕ) :
    canonicalC3CausalLogJetState s (left + 2) =
      causalUnitBracket (canonicalC3CausalLogJetState s) left -
        canonicalC3CausalLogJetState s left +
          2 • canonicalC3CausalLogJetState s (left + 1) :=
  rightLeg_eq_bracket_sub_left_add_two_center
    (canonicalC3CausalLogJetState s) left

/-- At every natural C3 cell, the causal logarithmic bracket is the existing
canonical log-bracket block. -/
theorem canonicalC3CausalLogJetBracket_eq_canonicalLogBracketBlock
    (m : ℕ) (s : ℂ) :
    causalUnitBracket (canonicalC3CausalLogJetState s) (3 * m + 1) =
      canonicalLogBracketBlock m s := by
  simp [causalUnitBracket, canonicalC3CausalLogJetState,
    canonicalLogBracketBlock]

/-- The value and log-jet sides of every sampled C3 cell therefore form one
commuting differentiation square. -/
theorem hasDerivAt_realCpSaturatedBracket_three_via_causalLogJet
    (m : ℕ) (s : ℂ) :
    HasDerivAt (realCpSaturatedBracket 3 m)
      (-canonicalLogBracketBlock m s) s := by
  have h := hasDerivAt_causalUnitBracket_value_eq_neg_logJet
    s (3 * m + 1)
  convert h using 1
  · funext u
    exact realCpSaturatedBracket_three_eq_causalUnitBracket m u
  · rw [canonicalC3CausalLogJetBracket_eq_canonicalLogBracketBlock]

/-! ## The same causal ledger in the centered-height coordinate -/

/-- The causal value state pulled back through `s = 1/2 + i z`. -/
def canonicalC3CausalHeightValueState (z : ℂ) : ℕ → ℂ :=
  canonicalC3CausalValueState (operatorHeightParameter z)

/-- The canonical height companion.  The factor `i` is forced by the chain
rule; it is not a normalization of the causal cells. -/
def canonicalC3CausalHeightCompanionState (z : ℂ) : ℕ → ℂ :=
  fun n => Complex.I *
    canonicalC3CausalLogJetState (operatorHeightParameter z) n

/-- In the height coordinate, the derivative of the value state is minus the
height companion. -/
theorem hasDerivAt_canonicalC3CausalHeightValueState_eq_neg_companion
    (z : ℂ) (n : ℕ) :
    HasDerivAt (fun u : ℂ => canonicalC3CausalHeightValueState u n)
      (-canonicalC3CausalHeightCompanionState z n) z := by
  have h :=
    (hasDerivAt_canonicalC3CausalValueState_eq_neg_logJet
      (operatorHeightParameter z) n).comp z
        (hasDerivAt_operatorHeightParameter z)
  simpa [Function.comp_def, canonicalC3CausalHeightValueState,
    canonicalC3CausalHeightCompanionState, mul_comm] using h

/-- The complete left--center--right bracket commutes with the height
derivative, with the same chain-rule rotation on all three coordinates. -/
theorem hasDerivAt_causalUnitBracket_heightValue_eq_neg_companion
    (z : ℂ) (left : ℕ) :
    HasDerivAt
      (fun u : ℂ =>
        causalUnitBracket (canonicalC3CausalHeightValueState u) left)
      (-causalUnitBracket
        (canonicalC3CausalHeightCompanionState z) left) z := by
  have hleft :=
    hasDerivAt_canonicalC3CausalHeightValueState_eq_neg_companion z left
  have hcenter :=
    hasDerivAt_canonicalC3CausalHeightValueState_eq_neg_companion z (left + 1)
  have hright :=
    hasDerivAt_canonicalC3CausalHeightValueState_eq_neg_companion z (left + 2)
  rw [show (fun u : ℂ =>
      causalUnitBracket (canonicalC3CausalHeightValueState u) left) =
      (fun u : ℂ =>
        canonicalC3CausalHeightValueState u left -
          2 * canonicalC3CausalHeightValueState u (left + 1) +
            canonicalC3CausalHeightValueState u (left + 2)) by
    funext u
    simp [causalUnitBracket, nsmul_eq_mul]]
  refine ((hleft.sub (hcenter.const_mul 2)).add hright).congr_deriv ?_
  simp only [causalUnitBracket, nsmul_eq_mul]
  ring

/-- Every sampled C3 cell acquires exactly the same height rotation as the
completed TFVD companion. -/
theorem canonicalC3CausalHeightCompanionBracket_eq_I_mul_logBracketBlock
    (m : ℕ) (z : ℂ) :
    causalUnitBracket (canonicalC3CausalHeightCompanionState z) (3 * m + 1) =
      Complex.I * canonicalLogBracketBlock m (operatorHeightParameter z) := by
  simp [canonicalC3CausalHeightCompanionState,
    canonicalC3CausalLogJetState, causalUnitBracket,
    canonicalLogBracketBlock]
  ring

/-! ## Chiral readout of a finite center--leg ledger -/

/-- The scalar wedge of one `(value, logJet)` pair is exactly its signed
chiral energy difference. -/
theorem scalarBoundaryWedge_eq_scalarChiralDifference
    (value logJet : ℂ) :
    scalarBoundaryWedge value logJet =
      Complex.I *
        (inner ℂ
            (completedScalarBoundaryPositivePolarization
              (WithLp.toLp 2 (logJet, value)))
            (completedScalarBoundaryPositivePolarization
              (WithLp.toLp 2 (logJet, value))) -
          inner ℂ
            (completedScalarBoundaryNegativePolarization
              (WithLp.toLp 2 (logJet, value)))
            (completedScalarBoundaryNegativePolarization
              (WithLp.toLp 2 (logJet, value)))) := by
  calc
    scalarBoundaryWedge value logJet =
        inner ℂ (WithLp.toLp 2 (logJet, value))
          (completedScalarBoundarySymplecticRotation
            (WithLp.toLp 2 (logJet, value))) := by
      simp [scalarBoundaryWedge,
        completedScalarBoundarySymplecticRotation_apply,
        WithLp.prod_inner_apply, RCLike.inner_apply]
      ring
    _ = _ :=
      inner_completedScalarBoundarySymplecticRotation_eq_chiralDifference
        (WithLp.toLp 2 (logJet, value))
        (WithLp.toLp 2 (logJet, value))

/-- Rotating a logarithmic jet by `i` converts the imaginary boundary wedge
into twice the real value--jet pairing.  This is the local algebra behind the
global radial-energy route. -/
theorem scalarBoundaryWedge_value_I_mul_logJet_im
    (value logJet : ℂ) :
    (scalarBoundaryWedge value (Complex.I * logJet)).im =
      2 * ((starRingEnd ℂ) value * logJet).re := by
  simp [scalarBoundaryWedge, Complex.mul_im, Complex.mul_re]
  ring

/-- Complete local center--leg ledger for the scalar completed trace. -/
def completedNativeFNegFPrimeLocalLegLedger
    {ι : Type*} [Fintype ι]
    (z : ℂ) (legs : ReflectedBoundarySynthesisData ι) : ℂ :=
  (∑ i : ι,
    sameSEdgeBoundaryWedge
      (legs.left i) (legs.right i)
      (legs.jetLeft i) (legs.jetRight i)) +
    twoLegBoundaryCrossProvenance
      legs.left legs.right legs.jetLeft legs.jetRight +
    reflectedBoundaryResidualCorrection
      (completedNativeOperatorCharacteristic z)
      (completedNativeOperatorBoundaryCompanion z) legs

/-- The completed `(F,-F')` chiral balance expanded through any finite local
four-leg ledger.  Center--leg synthesis determines the local terms; ordered
cross provenance and the four explicit synthesis residuals are retained. -/
theorem completedNativeFNegFPrime_chiralDifference_eq_localLegLedger
    {ι : Type*} [Fintype ι]
    (z : ℂ) (legs : ReflectedBoundarySynthesisData ι) :
    Complex.I *
        (inner ℂ
            (completedScalarBoundaryPositivePolarization
              (completedNativeFNegFPrimeBoundaryTraceState z))
            (completedScalarBoundaryPositivePolarization
              (completedNativeFNegFPrimeBoundaryTraceState z)) -
          inner ℂ
            (completedScalarBoundaryNegativePolarization
              (completedNativeFNegFPrimeBoundaryTraceState z))
            (completedScalarBoundaryNegativePolarization
              (completedNativeFNegFPrimeBoundaryTraceState z))) =
      (∑ i : ι,
        sameSEdgeBoundaryWedge
          (legs.left i) (legs.right i)
          (legs.jetLeft i) (legs.jetRight i)) +
        twoLegBoundaryCrossProvenance
          legs.left legs.right legs.jetLeft legs.jetRight +
        reflectedBoundaryResidualCorrection
          (completedNativeOperatorCharacteristic z)
          (completedNativeOperatorBoundaryCompanion z) legs := by
  change Complex.I *
      (inner ℂ
          (completedScalarBoundaryPositivePolarization
            (WithLp.toLp 2
              (completedNativeOperatorBoundaryCompanion z,
                completedNativeOperatorCharacteristic z)))
          (completedScalarBoundaryPositivePolarization
            (WithLp.toLp 2
              (completedNativeOperatorBoundaryCompanion z,
                completedNativeOperatorCharacteristic z))) -
        inner ℂ
          (completedScalarBoundaryNegativePolarization
            (WithLp.toLp 2
              (completedNativeOperatorBoundaryCompanion z,
                completedNativeOperatorCharacteristic z)))
          (completedScalarBoundaryNegativePolarization
            (WithLp.toLp 2
              (completedNativeOperatorBoundaryCompanion z,
                completedNativeOperatorCharacteristic z)))) = _
  rw [← scalarBoundaryWedge_eq_scalarChiralDifference]
  exact scalarBoundaryWedge_eq_localTwoLeg_add_cross_add_residualCorrection
    (completedNativeOperatorCharacteristic z)
    (completedNativeOperatorBoundaryCompanion z) legs

/-- Exact obstruction exposed by the previous expansion: reducing the
completed chiral balance to the sum of local center--leg wedges is equivalent
to cancellation of cross provenance with the explicit readout residual. -/
theorem completedNativeFNegFPrime_chiralDifference_eq_localLegs_iff
    {ι : Type*} [Fintype ι]
    (z : ℂ) (legs : ReflectedBoundarySynthesisData ι) :
    Complex.I *
          (inner ℂ
              (completedScalarBoundaryPositivePolarization
                (completedNativeFNegFPrimeBoundaryTraceState z))
              (completedScalarBoundaryPositivePolarization
                (completedNativeFNegFPrimeBoundaryTraceState z)) -
            inner ℂ
              (completedScalarBoundaryNegativePolarization
                (completedNativeFNegFPrimeBoundaryTraceState z))
              (completedScalarBoundaryNegativePolarization
                (completedNativeFNegFPrimeBoundaryTraceState z))) =
        ∑ i : ι,
          sameSEdgeBoundaryWedge
            (legs.left i) (legs.right i)
            (legs.jetLeft i) (legs.jetRight i) ↔
      twoLegBoundaryCrossProvenance
            legs.left legs.right legs.jetLeft legs.jetRight +
          reflectedBoundaryResidualCorrection
            (completedNativeOperatorCharacteristic z)
            (completedNativeOperatorBoundaryCompanion z) legs = 0 := by
  rw [completedNativeFNegFPrime_chiralDifference_eq_localLegLedger
    (ι := ι) z legs]
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

/-- The imaginary part of the complete local ledger is the unnormalized
Hermite--Biehler energy difference. -/
theorem completedNativeFNegFPrimeLocalLegLedger_im_eq_chiralNormDifference
    {ι : Type*} [Fintype ι]
    (z : ℂ) (legs : ReflectedBoundarySynthesisData ι) :
    (completedNativeFNegFPrimeLocalLegLedger z legs).im =
      ‖completedScalarBoundaryPositivePolarization
          (completedNativeFNegFPrimeBoundaryTraceState z)‖ ^ 2 -
        ‖completedScalarBoundaryNegativePolarization
          (completedNativeFNegFPrimeBoundaryTraceState z)‖ ^ 2 := by
  unfold completedNativeFNegFPrimeLocalLegLedger
  rw [← completedNativeFNegFPrime_chiralDifference_eq_localLegLedger
    (ι := ι) z legs]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  rw [Complex.I_mul_im]
  norm_cast

/-- Exact answer to the center--leg positivity question.  In the upper half
plane, diagonal `dslope` nonnegativity is equivalent to nonnegativity of the
imaginary part of the complete telescoped leg ledger.  Local cells alone are
insufficient unless their cross provenance and synthesis residual are also
controlled. -/
theorem completedNativePolarizedDslopeKernel_diagonal_re_nonneg_iff_localLegLedger
    {ι : Type*} [Fintype ι]
    {z : ℂ} (legs : ReflectedBoundarySynthesisData ι)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hzIm : 0 < z.im) :
    0 ≤ (canonicalCompletedNativePolarizedDslopeKernel z z).re ↔
      0 ≤ (completedNativeFNegFPrimeLocalLegLedger z legs).im := by
  rw [completedNativePolarizedDslopeKernel_diagonal_re_nonneg_iff_hermiteBiehler
    hzStrip hzF hzIm]
  have hpositive :=
    norm_sq_completedScalarBoundaryPositivePolarization
      (completedNativeFNegFPrimeBoundaryTraceState z)
  have hnegative :=
    norm_sq_completedScalarBoundaryNegativePolarization
      (completedNativeFNegFPrimeBoundaryTraceState z)
  rw [completedNativeFNegFPrime_positiveCombination] at hpositive
  rw [completedNativeFNegFPrime_negativeCombination] at hnegative
  rw [completedNativeFNegFPrimeLocalLegLedger_im_eq_chiralNormDifference
    (ι := ι) z legs]
  constructor <;> intro h <;> nlinarith

/-- Exact finite center--leg expansion: telescoping determines the local
cell wedges, while every ordered cross-cell pairing stays visible. -/
theorem scalarChiralDifference_sum_causalCells
    {ι : Type*} [Fintype ι]
    (value logJet : ℕ → ℂ) (cell : ι → ℕ) :
    Complex.I *
        (inner ℂ
            (completedScalarBoundaryPositivePolarization
              (WithLp.toLp 2
                (∑ i : ι, causalUnitBracket logJet (cell i),
                  ∑ i : ι, causalUnitBracket value (cell i))))
            (completedScalarBoundaryPositivePolarization
              (WithLp.toLp 2
                (∑ i : ι, causalUnitBracket logJet (cell i),
                  ∑ i : ι, causalUnitBracket value (cell i)))) -
          inner ℂ
            (completedScalarBoundaryNegativePolarization
              (WithLp.toLp 2
                (∑ i : ι, causalUnitBracket logJet (cell i),
                  ∑ i : ι, causalUnitBracket value (cell i))))
            (completedScalarBoundaryNegativePolarization
              (WithLp.toLp 2
                (∑ i : ι, causalUnitBracket logJet (cell i),
                  ∑ i : ι, causalUnitBracket value (cell i))))) =
      (∑ i : ι,
        scalarBoundaryWedge
          (causalUnitBracket value (cell i))
          (causalUnitBracket logJet (cell i))) +
        scalarBoundaryCrossProvenance
          (fun i : ι => causalUnitBracket value (cell i))
          (fun i : ι => causalUnitBracket logJet (cell i)) := by
  rw [← scalarBoundaryWedge_eq_scalarChiralDifference]
  exact scalarBoundaryWedge_sum_eq_local_add_crossProvenance
    (fun i : ι => causalUnitBracket value (cell i))
    (fun i : ι => causalUnitBracket logJet (cell i))

/-- Canonical specialization to all C3 cells retained by one cutoff.  This
is the exact place where left--center--right telescoping enters the chiral
boundary calculation. -/
theorem canonicalC3ScalarChiralDifference_eq_localCells_add_cross
    (M : ℕ) (s : ℂ) :
    Complex.I *
        (inner ℂ
            (completedScalarBoundaryPositivePolarization
              (WithLp.toLp 2
                (∑ m : Fin M, canonicalLogBracketBlock m s,
                  ∑ m : Fin M, realCpSaturatedBracket 3 m s)))
            (completedScalarBoundaryPositivePolarization
              (WithLp.toLp 2
                (∑ m : Fin M, canonicalLogBracketBlock m s,
                  ∑ m : Fin M, realCpSaturatedBracket 3 m s))) -
          inner ℂ
            (completedScalarBoundaryNegativePolarization
              (WithLp.toLp 2
                (∑ m : Fin M, canonicalLogBracketBlock m s,
                  ∑ m : Fin M, realCpSaturatedBracket 3 m s)))
            (completedScalarBoundaryNegativePolarization
              (WithLp.toLp 2
                (∑ m : Fin M, canonicalLogBracketBlock m s,
                  ∑ m : Fin M, realCpSaturatedBracket 3 m s)))) =
      (∑ m : Fin M,
        scalarBoundaryWedge
          (realCpSaturatedBracket 3 m s)
          (canonicalLogBracketBlock m s)) +
        scalarBoundaryCrossProvenance
          (fun m : Fin M => realCpSaturatedBracket 3 m s)
          (fun m : Fin M => canonicalLogBracketBlock m s) := by
  simpa only [realCpSaturatedBracket_three_eq_causalUnitBracket,
    canonicalC3CausalLogJetBracket_eq_canonicalLogBracketBlock] using
    (scalarChiralDifference_sum_causalCells
      (ι := Fin M)
      (canonicalC3CausalValueState s)
      (canonicalC3CausalLogJetState s)
      (fun m : Fin M => 3 * (m : ℕ) + 1))

/-! ## The complete ledger as one global radial energy -/

/-- The complete local/cross/residual ledger is independent of the chosen
finite synthesis presentation: its sum is exactly the completed scalar
boundary wedge. -/
theorem completedNativeFNegFPrimeLocalLegLedger_eq_scalarBoundaryWedge
    {ι : Type*} [Fintype ι]
    (z : ℂ) (legs : ReflectedBoundarySynthesisData ι) :
    completedNativeFNegFPrimeLocalLegLedger z legs =
      scalarBoundaryWedge
        (completedNativeOperatorCharacteristic z)
        (completedNativeOperatorBoundaryCompanion z) := by
  exact (scalarBoundaryWedge_eq_localTwoLeg_add_cross_add_residualCorrection
    (completedNativeOperatorCharacteristic z)
    (completedNativeOperatorBoundaryCompanion z) legs).symm

/-- Squared modulus of the completed characteristic along the transverse
height line through `z`. -/
def completedNativeVerticalModulusEnergy (z : ℂ) (y : ℝ) : ℝ :=
  ‖completedNativeOperatorCharacteristic
      (z + Complex.I * (y : ℂ))‖ ^ 2

/-- The derivative of the transverse modulus energy is exactly the imaginary
completed `(F,-F')` boundary wedge.  This packages local cells, ordered cross
terms, completion, and the readout residual before taking the sign. -/
theorem hasDerivAt_completedNativeVerticalModulusEnergy
    {z : ℂ} (hzDomain : z ∈ completedNativeHeightDomain) :
    HasDerivAt (completedNativeVerticalModulusEnergy z)
      (scalarBoundaryWedge
        (completedNativeOperatorCharacteristic z)
        (completedNativeOperatorBoundaryCompanion z)).im 0 := by
  have hcharacteristic :=
    (completedNativeOperatorCharacteristic_analyticAt hzDomain).differentiableAt.hasDerivAt
  have hline : HasDerivAt (fun u : ℂ => z + Complex.I * u) Complex.I 0 := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id (0 : ℂ)).const_mul Complex.I).const_add z
  have hcharacteristicAtLine :
      HasDerivAt completedNativeOperatorCharacteristic
        (deriv completedNativeOperatorCharacteristic z)
        (z + Complex.I * (0 : ℂ)) := by
    simpa using hcharacteristic
  have hcomplex := hcharacteristicAtLine.comp 0 hline
  have hreal := hcomplex.comp_ofReal
  have henergy := hreal.norm_sq
  convert henergy using 1
  · funext y
    rfl
  · simp [scalarBoundaryWedge,
      completedNativeOperatorBoundaryCompanion_eq_neg_deriv,
      Complex.mul_re, Complex.mul_im]
    ring

/-- The same identity written with any finite center--leg synthesis ledger.
No cancellation of cross or residual channels is requested. -/
theorem hasDerivAt_completedNativeVerticalModulusEnergy_eq_localLegLedger
    {ι : Type*} [Fintype ι]
    {z : ℂ} (hzDomain : z ∈ completedNativeHeightDomain)
    (legs : ReflectedBoundarySynthesisData ι) :
    HasDerivAt (completedNativeVerticalModulusEnergy z)
      (completedNativeFNegFPrimeLocalLegLedger z legs).im 0 := by
  rw [completedNativeFNegFPrimeLocalLegLedger_eq_scalarBoundaryWedge]
  exact hasDerivAt_completedNativeVerticalModulusEnergy hzDomain

/-- Route B in exact form: diagonal `dslope` nonnegativity is equivalent to
radial monotonicity of the one global completed modulus energy. -/
theorem
    completedNativePolarizedDslopeKernel_diagonal_re_nonneg_iff_verticalModulusEnergy
    {ι : Type*} [Fintype ι]
    {z : ℂ} (legs : ReflectedBoundarySynthesisData ι)
    (hzDomain : z ∈ completedNativeHeightDomain)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hzIm : 0 < z.im) :
    0 ≤ (canonicalCompletedNativePolarizedDslopeKernel z z).re ↔
      0 ≤ deriv (completedNativeVerticalModulusEnergy z) 0 := by
  rw [(hasDerivAt_completedNativeVerticalModulusEnergy_eq_localLegLedger
    hzDomain legs).deriv]
  exact
    completedNativePolarizedDslopeKernel_diagonal_re_nonneg_iff_localLegLedger
      legs hzDomain hzF hzIm

end

end CarrySelfAdjointOperator
