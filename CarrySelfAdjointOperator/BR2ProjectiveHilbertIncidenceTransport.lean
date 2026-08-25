import CarrySelfAdjointOperator.BR2BracketTfvdIncidenceTransport
import CPFormal.Analytic.CpNativeGpreTfvdProjectiveAnalysis
import Mathlib.Tactic

/-!
# BR2 incidence transport in the completed TFVD Hilbert carrier

The finite enriched TFVD carriers are camera atlases of one common completed
state, not unrelated targets.  Their concrete Hilbert model is the native
vertical space `CarryVerticalL2`.  This file records the exact commuting
square:

* a bracket incidence is realized faithfully in `CarryVerticalL2`;
* every finite TFVD analysis is the corresponding camera port of that state;
* the exact TFVD reconstruction recovers the same Hilbert vector;
* simultaneous projective analysis retains all finite atlases coherently.

All statements are global in the parity/order index.  No scalar readout,
spectral value, zero condition, cutoff limit, or primality hypothesis occurs.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open FiniteNativeCarryOperator.Camera
open NativeCarrySpectralWeyl.Camera
open scoped lp

noncomputable section

/-- Concrete infinite-dimensional Hilbert carrier underlying the completed
projective TFVD/Green analysis. -/
abbrev CanonicalCompletedTfvdGreenHilbertCarrier := CarryVerticalL2

/-- The complete incidence ledger realized directly in the common Hilbert
carrier, before selecting any finite camera atlas. -/
def br2CameraBracketProjectiveHilbertMap :
    (ℕ →₀ ℝ) →ₗ[ℝ] CanonicalCompletedTfvdGreenHilbertCarrier :=
  (nativeGpreCanonicalVerticalRealization.restrictScalars ℝ).comp
    br2RealIncidenceComplexification

@[simp] theorem br2CameraBracketProjectiveHilbertMap_cameraBracketIncidence
    (base radius index : ℕ) :
    br2CameraBracketProjectiveHilbertMap
        (cameraBracketIncidence base radius index) =
      br2CameraBracketVerticalState base radius index := by
  exact nativeGpreCanonicalVerticalRealization_cameraBracketIncidence
    base radius index

/-- The Hilbert realization loses no incidence coordinate. -/
theorem br2CameraBracketProjectiveHilbertMap_injective :
    Function.Injective br2CameraBracketProjectiveHilbertMap :=
  nativeGpreCanonicalVerticalRealization_injective.comp
    br2RealIncidenceComplexification_injective

/-- Parity-interleaved all-order bracket family in the single completed
Hilbert carrier. -/
def br2CameraBracketProjectiveHilbertParityJet
    (base radius : ℕ) :
    (ℕ ⊕ ℕ) → CanonicalCompletedTfvdGreenHilbertCarrier
  | Sum.inl n => br2CameraBracketVerticalState base radius (2 * n)
  | Sum.inr n => br2CameraBracketVerticalState base radius (2 * n + 1)

/-- The already constructed incidence transport therefore lands in the
concrete completed TFVD Hilbert carrier, globally in the order index. -/
def br2CameraBracketProjectiveHilbertIncidenceJetTransport
    (base radius : ℕ) :
    BR2BracketIncidenceJetTransport base radius
      (br2CameraBracketProjectiveHilbertParityJet base radius) where
  toLinearMap := br2CameraBracketProjectiveHilbertMap
  injective := br2CameraBracketProjectiveHilbertMap_injective
  even_eq n := by
    exact
      (br2CameraBracketProjectiveHilbertMap_cameraBracketIncidence
        base radius (2 * n)).symm
  odd_eq n := by
    exact
      (br2CameraBracketProjectiveHilbertMap_cameraBracketIncidence
        base radius (2 * n + 1)).symm

/-- The completed Hilbert carrier contains the complete independent even
incidence family. -/
theorem br2CameraBracketProjectiveHilbertParityJet_even_linearIndependent
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) :
    LinearIndependent ℝ
      (fun n : ℕ =>
        br2CameraBracketProjectiveHilbertParityJet
          base radius (Sum.inl n)) :=
  (br2CameraBracketProjectiveHilbertIncidenceJetTransport base radius).even_linearIndependent
    hbase hradius

/-- The completed Hilbert carrier contains the complete independent odd
incidence family. -/
theorem br2CameraBracketProjectiveHilbertParityJet_odd_linearIndependent
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) :
    LinearIndependent ℝ
      (fun n : ℕ =>
        br2CameraBracketProjectiveHilbertParityJet
          base radius (Sum.inr n)) :=
  (br2CameraBracketProjectiveHilbertIncidenceJetTransport base radius).odd_linearIndependent
    hbase hradius

/-- Exact real-linear TFVD reconstruction from one finite atlas. -/
def br2FiniteTfvdHilbertRecovery
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    NativeGpreFiniteTfvdAnalysisCarrier S →ₗ[ℝ]
      CanonicalCompletedTfvdGreenHilbertCarrier :=
  (nativeGpreFiniteTfvdReconstruction q hq0 hq1 S).toLinearMap.restrictScalars ℝ

/-- Analysis followed by exact reconstruction is the direct Hilbert
realization of the incidence ledger. -/
theorem br2FiniteTfvdHilbertRecovery_comp_analysisMap
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    (br2FiniteTfvdHilbertRecovery q hqpos.le hq1 S).comp
        (br2CameraBracketTfvdAnalysisMap q S) =
      br2CameraBracketProjectiveHilbertMap := by
  apply LinearMap.ext
  intro incidence
  exact nativeGpreFiniteTfvdReconstruction_analysis
    q hqpos hq1 S
      (nativeGpreCanonicalVerticalRealization
        (br2RealIncidenceComplexification incidence))

/-- Every parity/order component of the finite TFVD jet reconstructs to the
same component of the completed Hilbert jet. -/
theorem br2FiniteTfvdHilbertRecovery_parityJet
    (base radius : ℕ)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (i : ℕ ⊕ ℕ) :
    br2FiniteTfvdHilbertRecovery q hqpos.le hq1 S
        (br2CameraBracketTfvdParityJet base radius q S i) =
      br2CameraBracketProjectiveHilbertParityJet base radius i := by
  cases i <;>
    exact nativeGpreFiniteTfvdReconstruction_analysis q hqpos hq1 S _

/-- Simultaneous all-atlas TFVD analysis of the same completed Hilbert jet. -/
def br2CameraBracketProjectiveTfvdParityJet
    (base radius : ℕ) (q : ℝ) :
    (ℕ ⊕ ℕ) → NativeGpreTfvdProjectiveAnalysisCarrier :=
  fun i => nativeGpreTfvdProjectiveAnalysis q
    (br2CameraBracketProjectiveHilbertParityJet base radius i)

/-- At every finite atlas, the projective jet is literally the previously
constructed finite TFVD parity jet. -/
@[simp] theorem br2CameraBracketProjectiveTfvdParityJet_apply
    (base radius : ℕ) (q : ℝ)
    (i : ℕ ⊕ ℕ) (S : Finset NativeGpreBoundaryContext) :
    br2CameraBracketProjectiveTfvdParityJet base radius q i S =
      br2CameraBracketTfvdParityJet base radius q S i := by
  cases i <;> rfl

/-- The simultaneous projective analysis is injective and hence transports
the complete incidence family without collapsing any order. -/
def br2CameraBracketProjectiveTfvdIncidenceJetTransport
    (base radius : ℕ)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    BR2BracketIncidenceJetTransport base radius
      (br2CameraBracketProjectiveTfvdParityJet base radius q) where
  toLinearMap :=
    ((nativeGpreTfvdProjectiveAnalysis q).toLinearMap.restrictScalars ℝ).comp
      br2CameraBracketProjectiveHilbertMap
  injective :=
    (nativeGpreTfvdProjectiveAnalysis_injective q hqpos hq1).comp
      br2CameraBracketProjectiveHilbertMap_injective
  even_eq n := by
    apply funext
    intro S
    rw [br2CameraBracketProjectiveTfvdParityJet_apply]
    exact
      (br2CameraBracketTfvdAnalysisMap_cameraBracketIncidence
        base radius (2 * n) q S).symm
  odd_eq n := by
    apply funext
    intro S
    rw [br2CameraBracketProjectiveTfvdParityJet_apply]
    exact
      (br2CameraBracketTfvdAnalysisMap_cameraBracketIncidence
        base radius (2 * n + 1) q S).symm

/-- Simultaneous all-atlas analysis preserves the complete even family. -/
theorem br2CameraBracketProjectiveTfvdParityJet_even_linearIndependent
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    LinearIndependent ℝ
      (fun n : ℕ =>
        br2CameraBracketProjectiveTfvdParityJet
          base radius q (Sum.inl n)) :=
  (br2CameraBracketProjectiveTfvdIncidenceJetTransport
    base radius q hqpos hq1).even_linearIndependent hbase hradius

/-- Simultaneous all-atlas analysis preserves the complete odd family. -/
theorem br2CameraBracketProjectiveTfvdParityJet_odd_linearIndependent
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    LinearIndependent ℝ
      (fun n : ℕ =>
        br2CameraBracketProjectiveTfvdParityJet
          base radius q (Sum.inr n)) :=
  (br2CameraBracketProjectiveTfvdIncidenceJetTransport
    base radius q hqpos hq1).odd_linearIndependent hbase hradius

/-- Projective compatibility is inherited from the one common Hilbert state,
for every parity/order component. -/
theorem br2CameraBracketProjectiveTfvdParityJet_compatible
    (base radius : ℕ) (q : ℝ) (i : ℕ ⊕ ℕ) :
    NativeGpreTfvdProjectiveCompatible
      (br2CameraBracketProjectiveTfvdParityJet base radius q i) :=
  nativeGpreTfvdProjectiveAnalysis_compatible q _

end

end CarrySelfAdjointOperator
