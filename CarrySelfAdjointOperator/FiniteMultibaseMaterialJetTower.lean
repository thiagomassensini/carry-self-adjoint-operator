import CarrySelfAdjointOperator.FiniteMaterialClockJets
import CarrySelfAdjointOperator.FiniteNativeDepthRawCameraGram
import CarrySelfAdjointOperator.C2LiteralCameraAllOrderJetCrosswalk

/-! Physical camera rows in their common material Hilbert carrier. All jet
orders use the existing logarithmic clock. This does not identify the positive
physical row Gram with the signed completed-source form. -/

noncomputable section
open scoped BigOperators InnerProduct ComplexConjugate Topology Matrix ComplexOrder
namespace CarrySelfAdjointOperator.MaterialCameraJets
open CPFormal.Analytic.Cp
open FiniteClockJets NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera NativeCarrySpectralWeyl.Camera.FiniteBridge
open NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Limits

/-- Jet power of the existing physical material clock, without temporal phases. -/
def materialJet {N : ℕ} (r : ℕ) (x : FiniteRealSpectralHilbert N) :
    FiniteRealSpectralHilbert N := (finiteMaterialClock N ^ r) x

theorem materialJet_apply {N : ℕ} (r : ℕ) (x : FiniteRealSpectralHilbert N) (n : Fin N) :
    materialJet r x n = (finiteRealSpectralFrequency n : ℂ) ^ r * x n := by
  induction r with
  | zero => simp [materialJet]
  | succ r ih =>
    simp only [materialJet, pow_succ', Module.End.mul_apply,
      finiteRealSpectralGenerator_apply]
    change (finiteRealSpectralFrequency n : ℂ) * materialJet r x n = _
    rw [ih]
    ring

theorem materialJet_add_order {N : ℕ} (r s : ℕ) (x : FiniteRealSpectralHilbert N) :
    materialJet r (materialJet s x) = materialJet (r + s) x := by
  simp [materialJet, pow_add, Module.End.mul_apply]

/-- Mathlib conjugates the first argument; the real diagonal moves across it. -/
theorem materialJet_pairing {N : ℕ} (r s : ℕ) (x y : FiniteRealSpectralHilbert N) :
    inner ℂ (materialJet r x) (materialJet s y) =
      inner ℂ x (materialJet (r + s) y) := by
  have hs := (finiteRealSpectralGenerator_isSymmetric N).pow r
  exact (hs x (materialJet s y)).trans
    (congrArg (inner ℂ x) (materialJet_add_order r s y))

/-- Actual time derivatives retain the exact (-i)^r phase of the unitary orbit. -/
theorem materialOrbit_derivative_eq_phasedJet {N : ℕ} (r : ℕ)
    (x : FiniteRealSpectralHilbert N) :
    iteratedDeriv r (fun t : ℝ => finiteMaterialOrbit N t x) 0 =
      (-Complex.I) ^ r • materialJet r x := by
  rw [finiteMaterialClockJet_eq_generatorPow]
  ext n
  rw [finiteClockStrongGenerator_pow_apply]
  change clockRate n ^ r * x n = (-Complex.I)^r * materialJet r x n
  rw [materialJet_apply]
  simp only [clockRate, mul_pow, mul_assoc]

/-- The literal coefficient row, with material position n+1, in a common carrier. -/
def literalCameraVector {ι : Type*} [Fintype ι]
    (M : ℕ) (camera : ι → ℕ) (b : ι) :
    FiniteRealSpectralHilbert (finiteFamilyWindow M camera) :=
  WithLp.toLp 2 (fun n => (finiteLiteralCameraMatrix M camera b n : ℂ))

/-- Mixed jet pairing of literal rows; no amplitude dressing or cutoff division. -/
def materialCameraPairing {ι : Type*} [Fintype ι]
    (M : ℕ) (camera : ι → ℕ) (r s : ℕ) (b c : ι) : ℂ :=
  inner ℂ (materialJet r (literalCameraVector M camera b))
    (materialJet s (literalCameraVector M camera c))

/-- Finite camera synthesis, retaining the whole material vector before pairing. -/
def materialCameraSynthesis {ι : Type*} [Fintype ι] (M : ℕ) (camera : ι → ℕ) :
    (ι → ℂ) →ₗ[ℂ] FiniteRealSpectralHilbert (finiteFamilyWindow M camera) where
  toFun a := ∑ b, a b • literalCameraVector M camera b
  map_add' a z := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' k a := by simp [Finset.smul_sum, mul_smul]

/-- All ordered camera crosses are retained under arbitrary coefficient changes. -/
theorem materialCameraSynthesis_jet_pairing {ι : Type*} [Fintype ι]
    (M : ℕ) (camera : ι → ℕ) (r s : ℕ) (a z : ι → ℂ) :
    inner ℂ (materialJet r (materialCameraSynthesis M camera a))
      (materialJet s (materialCameraSynthesis M camera z)) =
      ∑ b, ∑ c, conj (a b) * z c * materialCameraPairing M camera r s b c := by
  simp only [materialCameraSynthesis, LinearMap.coe_mk, AddHom.coe_mk, materialJet,
    map_sum, map_smul]
  rw [sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  simp only [materialCameraPairing, materialJet]
  ring

/-- Full jet Gram indexed by camera and derivative order. -/
def materialJetGram {ι : Type*} [Fintype ι] (M : ℕ) (camera : ι → ℕ) (r : ℕ) :
    Matrix (ι × Fin (r+1)) (ι × Fin (r+1)) ℂ :=
  fun b c => materialCameraPairing M camera b.2.val c.2.val b.1 c.1

/-- Intrinsic PSD of the finite physical jet family, without completed-source claims. -/
theorem materialJetGram_posSemidef {ι : Type*} [Fintype ι]
    (M : ℕ) (camera : ι → ℕ) (r : ℕ) : (materialJetGram M camera r).PosSemidef := by
  let V : Matrix (Fin (finiteFamilyWindow M camera)) (ι × Fin (r+1)) ℂ :=
    fun n p => materialJet p.2.val (literalCameraVector M camera p.1) n
  have he : materialJetGram M camera r = Vᴴ * V := by
    ext b c
    simp only [materialJetGram, materialCameraPairing, PiLp.inner_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, V, RCLike.inner_apply, starRingEnd_apply]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self V

theorem materialCameraPairing_add_order {ι : Type*} [Fintype ι]
    (M : ℕ) (camera : ι → ℕ) (r s : ℕ) (b c : ι) :
    materialCameraPairing M camera r s b c =
      materialCameraPairing M camera 0 (r + s) b c := by
  simpa [materialCameraPairing, materialJet] using
    materialJet_pairing r s (literalCameraVector M camera b) (literalCameraVector M camera c)

/-- Explicit signed cross sum for every order; no cross terms are omitted. -/
theorem materialCameraPairing_eq_logWeightedSum {ι : Type*} [Fintype ι]
    (M : ℕ) (camera : ι → ℕ) (r s : ℕ) (b c : ι) :
    materialCameraPairing M camera r s b c =
      ∑ n : Fin (finiteFamilyWindow M camera),
        ((finiteCoefficientAt (camera b) M n.val * finiteCoefficientAt (camera c) M n.val : ℝ) : ℂ) *
          (Real.log ((n.val + 1 : ℕ) : ℝ) : ℂ) ^ (r + s) := by
  rw [materialCameraPairing, materialJet_pairing, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro n hn
  simp [materialJet_apply, literalCameraVector, finiteLiteralCameraMatrix,
    finiteRealSpectralFrequency, RCLike.inner_apply]
  ring

/-- Order zero is exactly the existing raw literal physical Gram. -/
theorem materialCameraPairing_zero_eq_literalGram {ι : Type*} [Fintype ι]
    (M : ℕ) (camera : ι → ℕ) (hc : ∀ b, 2 ≤ camera b) (b c : ι) :
    materialCameraPairing M camera 0 0 b c =
      (literalFiniteCameraGram M (camera b) (camera c) : ℂ) := by
  rw [← finiteLiteralCameraMatrix_rowGram_apply_eq_literalFiniteCameraGram hc M b c]
  simp only [materialCameraPairing_eq_logWeightedSum, Nat.add_zero, pow_zero, mul_one]
  simp [finiteCameraRowGram, Matrix.mul_apply, finiteLiteralCameraMatrix,
    Matrix.transpose_apply, Complex.ofReal_sum]

/-- The physical cutoff defect is the existing centered-core plus boundary residue. -/
theorem materialCameraPairing_zero_eq_periodicGram_add_residue {ι : Type*} [Fintype ι]
    (M period : ℕ) (camera : ι → ℕ) (hc : ∀ b, 2 ≤ camera b) (b c : ι) :
    materialCameraPairing M camera 0 0 b c =
      ((M : ℝ) * periodicGramMatrix period camera b c +
        exactCutoffCameraGramResidue period M (camera b) (camera c) : ℝ) := by
  rw [materialCameraPairing_zero_eq_literalGram M camera hc b c,
    literalFiniteCameraGram_eq_periodicGram_add_residue hc b c]

/-- Period 420 supplies the exact linear part, while the physical defect is retained. -/
theorem materialCameraPairing_six_zero_exact (M : ℕ) (b c : Fin 6) :
    materialCameraPairing M sixCamera 0 0 b c =
      ((M : ℝ) * sixCameraGram b c +
        exactCutoffCameraGramResidue 420 M (sixCamera b) (sixCamera c) : ℝ) := by
  rw [materialCameraPairing_zero_eq_periodicGram_add_residue M 420 sixCamera
    (by intro i; simp [sixCamera]) b c]
  rw [sixCameraGram_eq]

/-- A concrete compatible order-zero defect: at M=1, C2 energy is 7 rather than 6. -/
theorem materialCameraPairing_six_one_c2_defect :
    materialCameraPairing 1 sixCamera 0 0 0 0 = (sixCameraGram 0 0 : ℂ) + 1 := by
  rw [materialCameraPairing_zero_eq_literalGram 1 sixCamera
    (by intro i; simp [sixCamera]) 0 0]
  have hGram : literalFiniteCameraGram 1 2 2 = 7 := by
    norm_num only [literalFiniteCameraGram, pairFiniteWindow, finiteCameraWindow,
      cameraBoundaryWidth, cameraSlope, finiteCoefficientAt, finiteCoefficient,
      seedCoefficient, centerCoefficient, bracketCoefficient,
      FiniteNativeCarryOperator.Camera.alignedCenter, Finset.sum_range_succ,
      ite_true, ite_false, Finset.sum_range_zero, add_zero, zero_add, min_self]
  change (literalFiniteCameraGram 1 2 2 : ℂ) = _
  rw [hGram]
  norm_num [sixCameraGram, sixCameraGramRat]

/-- Normalized six-camera order-zero pairing converges to the established Gram. -/
theorem materialCameraPairing_six_zero_tendsto (b c : Fin 6) :
    Filter.Tendsto
      (fun M : ℕ => (M : ℂ)⁻¹ * materialCameraPairing M sixCamera 0 0 b c)
      Filter.atTop (nhds (sixCameraGram b c : ℂ)) := by
  have hc : ∀ i : Fin 6, 2 ≤ sixCamera i := by intro i; simp [sixCamera]
  have h := tendsto_normalizedLiteralFiniteCameraGram_apply
    (period := 420) (camera := sixCamera) (by norm_num) hc sixCamera_commonPeriod b c
  have he := congr_fun (congr_fun sixCameraGram_eq b) c
  have ht := Complex.continuous_ofReal.continuousAt.tendsto.comp h
  simp_rw [materialCameraPairing_zero_eq_literalGram _ sixCamera hc b c]
  simpa [Function.comp_def, he] using ht

/-- Jet-generated subspace through order r, preserving the camera label. -/
def materialJetTower {ι : Type*} [Fintype ι]
    (M : ℕ) (camera : ι → ℕ) (r : ℕ) :
    Submodule ℂ (FiniteRealSpectralHilbert (finiteFamilyWindow M camera)) :=
  Submodule.span ℂ {x | ∃ b : ι, ∃ j : ℕ, j ≤ r ∧
    x = materialJet j (literalCameraVector M camera b)}

theorem materialJetTower_mono {ι : Type*} [Fintype ι]
    (M : ℕ) (camera : ι → ℕ) {r s : ℕ} (hrs : r ≤ s) :
    materialJetTower M camera r ≤ materialJetTower M camera s := by
  apply Submodule.span_mono
  rintro x ⟨b, j, hj, rfl⟩
  exact ⟨b, j, hj.trans hrs, rfl⟩

/-- The clock takes the whole generated subspace into the next-order subspace. -/
theorem materialClock_maps_jetTower {ι : Type*} [Fintype ι]
    (M : ℕ) (camera : ι → ℕ) (r : ℕ) :
    materialJetTower M camera r ≤
      (materialJetTower M camera (r + 1)).comap
        (finiteMaterialClock (finiteFamilyWindow M camera)) := by
  apply Submodule.span_le.mpr
  rintro x ⟨b, j, hj, rfl⟩
  apply Submodule.subset_span
  refine ⟨b, j + 1, by omega, ?_⟩
  simp [materialJet, pow_succ', Module.End.mul_apply]

/-- Positivity of the finite vector family is intrinsic, at every order. -/
theorem materialJetFamily_energy_nonneg {ι : Type*} [Fintype ι]
    (M : ℕ) (camera : ι → ℕ) (r : ℕ) (a : ι × Fin (r+1) → ℂ) :
    0 ≤ (inner ℂ
      (∑ p : ι × Fin (r+1), a p • materialJet p.2.val (literalCameraVector M camera p.1))
      (∑ p : ι × Fin (r+1), a p • materialJet p.2.val (literalCameraVector M camera p.1))).re :=
  inner_self_nonneg (𝕜 := ℂ)

end CarrySelfAdjointOperator.MaterialCameraJets
