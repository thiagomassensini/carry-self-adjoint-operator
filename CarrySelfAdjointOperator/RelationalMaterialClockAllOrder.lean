import CarrySelfAdjointOperator.FiniteMaterialTfvdJetTransport
import CarrySelfAdjointOperator.MultibaseCameraLogTfvdChannelTransport

/-! The existing relational camera-log ledger generates every material clock
power by FULL ordered word synthesis. Voice labels, physical camera labels,
material positions and jet order are retained as separate indices. This does
not identify the prime-voice axes with the physical profile Gram axes. -/

noncomputable section
open scoped BigOperators
namespace CarrySelfAdjointOperator.MaterialCameraJets
open CPFormal.Analytic.Cp NativeCarryC3Crosswalk

/-- All relation-derived voices present at a material integer. -/
abbrev RelationalLogVoice (n : ℕ) := ↥n.factorization.support

/-- Ordered camera-voice words; repeated labels and all mixed words survive. -/
abbrev RelationalLogWord (n r : ℕ) := Fin r → RelationalLogVoice n

theorem relationalLogVoice_synthesis {n : ℕ} (hn : n ≠ 0) :
    (∑ p : RelationalLogVoice n, cameraLogContributionVectorComplex n p.val) =
      (Real.log n : ℂ) := by
  rw [Finset.sum_coe_sort]
  have h := cameraComplexSynthesis_cameraLogContributionVectorComplex n
  rw [cameraComplexSynthesis, cameraLogContributionVectorComplex,
    Finsupp.linearCombination_onFinset] at h
  simp only [smul_eq_mul, mul_one] at h
  rw [primeDepthLogLedger_eq_log hn] at h
  exact h

/-- Relation-derived weight of a full ordered word, before scalar synthesis. -/
def relationalLogWordAmplitude (n r : ℕ) (word : RelationalLogWord n r) : ℂ :=
  ∏ j : Fin r, cameraLogContributionVectorComplex n (word j).val

/-- Every power is the exact sum of every ordered mixed word. -/
theorem relationalLogWord_synthesis {n : ℕ} (hn : n ≠ 0) (r : ℕ) :
    (∑ word : RelationalLogWord n r, relationalLogWordAmplitude n r word) =
      (Real.log n : ℂ)^r := by
  rw [← relationalLogVoice_synthesis hn, Fintype.sum_pow]
  rfl

/-- Full finite material jet fibres, retaining every voice word per coordinate. -/
def relationalWordJet {N : ℕ} (r : ℕ) (x : FiniteRealSpectralHilbert N) :
    (n : Fin N) → RelationalLogWord (n.val+1) r → ℂ :=
  fun n word => relationalLogWordAmplitude (n.val+1) r word * x n

/-- Only after assembling the full word family, synthesize into the existing Hilbert carrier. -/
def relationalWordJetSynthesis (N r : ℕ)
    (u : (n : Fin N) → RelationalLogWord (n.val+1) r → ℂ) : FiniteRealSpectralHilbert N :=
  WithLp.toLp 2 (fun n => ∑ word, u n word)

/-- Relational all-order synthesis is the original material clock power, not a fitted operator. -/
theorem relationalWordJetSynthesis_eq_materialJet (N r : ℕ) (x : FiniteRealSpectralHilbert N) :
    relationalWordJetSynthesis N r (relationalWordJet r x) = materialJet r x := by
  ext n
  change (∑ word : RelationalLogWord (n.val+1) r,
    relationalLogWordAmplitude (n.val+1) r word * x n) = materialJet r x n
  rw [← Finset.sum_mul, relationalLogWord_synthesis (by omega : n.val+1 ≠ 0)]
  exact (materialJet_apply r x n).symm

/-- Physical camera masks act on all relation words without privileging a voice. -/
theorem relationalWordJet_cameraMaterialAction {N : ℕ} (b M r : ℕ)
    (x : FiniteRealSpectralHilbert N) (n : Fin N) (word : RelationalLogWord (n.val+1) r) :
    relationalWordJet r (cameraMaterialAction b M x) n word =
      (NativeCarrySpectralWeyl.Camera.FiniteBridge.finiteCoefficient b M (n.val+1) : ℂ) *
        relationalWordJet r x n word := by
  simp only [relationalWordJet, cameraMaterialAction_apply]
  ring

/-- The actual physical camera jet is generated from its complete relational word fibres. -/
theorem relationalCameraWordJet_synthesis {N : ℕ} (b M r : ℕ)
    (x : FiniteRealSpectralHilbert N) :
    relationalWordJetSynthesis N r (relationalWordJet r (cameraMaterialAction b M x)) =
      materialJet r (cameraMaterialAction b M x) :=
  relationalWordJetSynthesis_eq_materialJet N r _

end CarrySelfAdjointOperator.MaterialCameraJets
