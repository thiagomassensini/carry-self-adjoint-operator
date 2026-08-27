import CarrySelfAdjointOperator.BR2ProjectiveHilbertIncidenceTransport
import GreenFrame.Concrete.Analysis.CanonicalTowerChart
import GreenFrame.Concrete.Analysis.ConcreteSplitBounds
import Mathlib.Data.PNat.Equiv
import Mathlib.Tactic

/-!
# BR2 incidence transport through the concrete all-bases Green frame

The completed TFVD carrier and the concrete Green-frame state are the same
square-summable sequence after the canonical reindexing `Nat equiv PNat`.
This file records that reindexing isometrically, then composes the faithful
BR2 incidence realization with the concrete all-bases Green analysis.

The target retains the full split carrier: seed, residual, depth-one Green,
and bulk Green channels.  No scalar readout, zero condition, spectral
specialization, or prime-indexed hypothesis is used.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open FiniteNativeCarryOperator.Camera
open GreenFrame.Concrete
open NativeCarrySpectralWeyl.Camera
open scoped lp

noncomputable section

/-! ## Canonical reindexing of the completed TFVD state -/

/-- Reindex a completed TFVD state from natural coordinates to positive
natural coordinates. -/
def carryVerticalL2ToGreenFrameStateValue
    (x : CarryVerticalL2) : State :=
  ⟨fun n : PNat ↦ x n.natPred, by
    apply memℓp_gen
    have hx : Summable
        (fun n : ℕ ↦ ‖x n‖ ^ (2 : ENNReal).toReal) :=
      (lp.memℓp x).summable (by norm_num)
    simpa [Function.comp_def] using
      (Equiv.pnatEquivNat.summable_iff.mpr hx)⟩

/-- Reindex a concrete Green-frame state back to natural coordinates. -/
def greenFrameStateToCarryVerticalL2Value
    (x : State) : CarryVerticalL2 :=
  ⟨fun n : ℕ ↦ x n.succPNat, by
    apply memℓp_gen
    have hx : Summable
        (fun n : PNat ↦ ‖x n‖ ^ (2 : ENNReal).toReal) :=
      (lp.memℓp x).summable (by norm_num)
    simpa [Function.comp_def] using
      (Equiv.pnatEquivNat.symm.summable_iff.mpr hx)⟩

@[simp] theorem carryVerticalL2ToGreenFrameStateValue_apply
    (x : CarryVerticalL2) (n : PNat) :
    carryVerticalL2ToGreenFrameStateValue x n = x n.natPred :=
  rfl

@[simp] theorem greenFrameStateToCarryVerticalL2Value_apply
    (x : State) (n : ℕ) :
    greenFrameStateToCarryVerticalL2Value x n = x n.succPNat :=
  rfl

private def carryVerticalL2GreenFrameStateLinearEquiv :
    CarryVerticalL2 ≃ₗ[ℂ] State where
  toFun := carryVerticalL2ToGreenFrameStateValue
  invFun := greenFrameStateToCarryVerticalL2Value
  left_inv x := by
    apply lp.ext
    funext n
    simp [carryVerticalL2ToGreenFrameStateValue,
      greenFrameStateToCarryVerticalL2Value]
  right_inv x := by
    apply lp.ext
    funext n
    simp [carryVerticalL2ToGreenFrameStateValue,
      greenFrameStateToCarryVerticalL2Value]
  map_add' x y := by
    apply lp.ext
    funext n
    rfl
  map_smul' c x := by
    apply lp.ext
    funext n
    rfl

private theorem carryVerticalL2ToGreenFrameStateValue_norm
    (x : CarryVerticalL2) :
    ‖carryVerticalL2ToGreenFrameStateValue x‖ = ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num),
    lp.norm_eq_tsum_rpow (by norm_num)]
  simp only [carryVerticalL2ToGreenFrameStateValue_apply]
  congr 1
  exact Equiv.pnatEquivNat.tsum_eq
    (fun n : ℕ ↦ ‖x n‖ ^ (2 : ENNReal).toReal)

/-- Canonical complex-linear isometric identification of the completed TFVD
carrier with the state space used by the concrete all-bases Green frame. -/
def carryVerticalL2GreenFrameStateEquiv :
    CarryVerticalL2 ≃ₗᵢ[ℂ] State :=
  LinearIsometryEquiv.mk carryVerticalL2GreenFrameStateLinearEquiv
    carryVerticalL2ToGreenFrameStateValue_norm

@[simp] theorem carryVerticalL2GreenFrameStateEquiv_apply
    (x : CarryVerticalL2) (n : PNat) :
    carryVerticalL2GreenFrameStateEquiv x n = x n.natPred :=
  rfl

/-! ## Faithful all-bases Green analysis -/

/-- The concrete all-bases Green-frame coefficient carrier, with the external
and bulk channels retained as an orthogonal direct sum. -/
abbrev CanonicalCompletedGreenFrameCarrier := ConcreteAnalysisSpace

/-- Completed TFVD state followed by the raw concrete all-bases Green
analysis.  The raw analysis is used so its four structural channel groups
remain literal coordinates. -/
def canonicalCompletedGreenFrameAnalysis :
    CarryVerticalL2 →ₗ[ℂ] CanonicalCompletedGreenFrameCarrier :=
  (concreteAnalysisOperator canonicalCarryInfinitePartition).toLinearMap.comp
    carryVerticalL2GreenFrameStateEquiv.toLinearEquiv.toLinearMap

/-- The Green-frame image retains the literal nested Hilbert split
`((seed,residual), depth-one Green), bulk Green`. -/
theorem canonicalCompletedGreenFrameAnalysis_apply
    (x : CarryVerticalL2) :
    canonicalCompletedGreenFrameAnalysis x =
      WithLp.toLp 2
        (WithLp.toLp 2
          (seedResidualAnalysis canonicalCarryInfinitePartition
              (carryVerticalL2GreenFrameStateEquiv x),
            greenDepthOneSectorAnalysis canonicalCarryInfinitePartition
              (carryVerticalL2GreenFrameStateEquiv x)),
          greenBulkSectorAnalysis canonicalCarryInfinitePartition
            (carryVerticalL2GreenFrameStateEquiv x)) := by
  rfl

/-- The concrete all-bases Green analysis is injective by its proved lower
frame bound `1 / 2`. -/
theorem concreteCanonicalGreenFrameAnalysis_injective :
    Function.Injective
      (concreteAnalysisOperator canonicalCarryInfinitePartition) := by
  intro x y hxy
  have hzero :
      concreteAnalysisOperator canonicalCarryInfinitePartition (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hbound :=
    (concreteSplitFrameBounds canonicalCarryInfinitePartition).lower_norm_sq
      (x - y)
  rw [hzero] at hbound
  simp only [concreteSplitFrameBounds_lower, norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hbound
  have hnorm : ‖x - y‖ = 0 := by
    nlinarith [sq_nonneg ‖x - y‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- The completed TFVD-to-Green analysis loses no Hilbert state. -/
theorem canonicalCompletedGreenFrameAnalysis_injective :
    Function.Injective canonicalCompletedGreenFrameAnalysis :=
  concreteCanonicalGreenFrameAnalysis_injective.comp
    carryVerticalL2GreenFrameStateEquiv.injective

/-- Every concrete Green stencil is exactly the normalized TFVD readout of
the same reindexed completed state. -/
theorem carryVerticalL2_greenStencil_eq_normalizedTowerTFVD
    (e : GreenEvent) (x : CarryVerticalL2) :
    verticalGreenStencil e (carryVerticalL2GreenFrameStateEquiv x) =
      normalizedTowerTFVD (canonicalTowerEvent e)
        (carryVerticalL2GreenFrameStateEquiv x) :=
  verticalGreenStencil_eq_canonicalNormalizedTowerTFVD e _

/-! ## Global all-order BR2 transport -/

/-- The complete bracket-incidence parity family analyzed in the concrete
all-bases Green carrier. -/
def br2CameraBracketGreenFrameParityJet
    (base radius : ℕ) :
    (ℕ ⊕ ℕ) → CanonicalCompletedGreenFrameCarrier :=
  fun i ↦ canonicalCompletedGreenFrameAnalysis
    (br2CameraBracketProjectiveHilbertParityJet base radius i)

/-- Faithful all-order transport from bracket incidences into the concrete
all-bases Green-frame carrier. -/
def br2CameraBracketGreenFrameIncidenceJetTransport
    (base radius : ℕ) :
    BR2BracketIncidenceJetTransport base radius
      (br2CameraBracketGreenFrameParityJet base radius) where
  toLinearMap :=
    (canonicalCompletedGreenFrameAnalysis.restrictScalars ℝ).comp
      br2CameraBracketProjectiveHilbertMap
  injective := canonicalCompletedGreenFrameAnalysis_injective.comp
    br2CameraBracketProjectiveHilbertMap_injective
  even_eq n := by
    change canonicalCompletedGreenFrameAnalysis
        (br2CameraBracketVerticalState base radius (2 * n)) =
      canonicalCompletedGreenFrameAnalysis
        (br2CameraBracketProjectiveHilbertMap
          (cameraBracketIncidence base radius (2 * n)))
    rw [br2CameraBracketProjectiveHilbertMap_cameraBracketIncidence]
  odd_eq n := by
    change canonicalCompletedGreenFrameAnalysis
        (br2CameraBracketVerticalState base radius (2 * n + 1)) =
      canonicalCompletedGreenFrameAnalysis
        (br2CameraBracketProjectiveHilbertMap
          (cameraBracketIncidence base radius (2 * n + 1)))
    rw [br2CameraBracketProjectiveHilbertMap_cameraBracketIncidence]

/-- The concrete all-bases Green carrier preserves the complete even bracket
family. -/
theorem br2CameraBracketGreenFrameParityJet_even_linearIndependent
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) :
    LinearIndependent ℝ
      (fun n : ℕ ↦
        br2CameraBracketGreenFrameParityJet base radius (Sum.inl n)) :=
  (br2CameraBracketGreenFrameIncidenceJetTransport base radius).even_linearIndependent
    hbase hradius

/-- The concrete all-bases Green carrier preserves the complete odd bracket
family. -/
theorem br2CameraBracketGreenFrameParityJet_odd_linearIndependent
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) :
    LinearIndependent ℝ
      (fun n : ℕ ↦
        br2CameraBracketGreenFrameParityJet base radius (Sum.inr n)) :=
  (br2CameraBracketGreenFrameIncidenceJetTransport base radius).odd_linearIndependent
    hbase hradius

end

end CarrySelfAdjointOperator
