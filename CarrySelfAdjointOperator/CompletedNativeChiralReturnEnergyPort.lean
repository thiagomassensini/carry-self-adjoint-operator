import CarrySelfAdjointOperator.CompletedNativeChiralReturnSevenSampleStorage
import Mathlib.Algebra.Algebra.Basic
import CarrySelfAdjointOperator.CompletedNativeChiralJetStorageTransport
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Source-derived energy ports for the complete chiral return

The defect is computed from the original finite return transfer on its incident
span, with the inherited Cauchy inner product. No moment Gram defines the port.
A positive factorization is used only after source contractivity is proved.
The unconditional application in this module is the existing seven-source sector.
-/
namespace CarrySelfAdjointOperator.ChiralReturn
open scoped BigOperators ComplexConjugate InnerProductSpace CStarAlgebra
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

local instance incidentFinite (k N : ℕ) : FiniteDimensional ℂ (RadialIncidentSpan k N) :=
  (radialIncidentSynthesis k N).finiteDimensional_range

local instance incidentEndComm (k N : ℕ) :
    SMulCommClass ℝ (RadialIncidentSpan k N →L[ℂ] RadialIncidentSpan k N)
      (RadialIncidentSpan k N →L[ℂ] RadialIncidentSpan k N) :=
  ⟨fun r f g => by
    apply ContinuousLinearMap.ext
    intro x
    change r • f (g x) = f (r • g x)
    exact (ContinuousLinearMap.map_smul_of_tower f r (g x)).symm⟩

local instance incidentEndTower (k N : ℕ) :
    IsScalarTower ℝ (RadialIncidentSpan k N →L[ℂ] RadialIncidentSpan k N)
      (RadialIncidentSpan k N →L[ℂ] RadialIncidentSpan k N) :=
  ⟨fun r f g => by apply ContinuousLinearMap.ext; intro x; rfl⟩

local instance incidentEndComplexComm (k N : ℕ) :
    SMulCommClass ℂ (RadialIncidentSpan k N →L[ℂ] RadialIncidentSpan k N)
      (RadialIncidentSpan k N →L[ℂ] RadialIncidentSpan k N) :=
  ⟨fun r f g => by
    apply ContinuousLinearMap.ext
    intro x
    exact (map_smul f r (g x)).symm⟩

local instance incidentEndComplexTower (k N : ℕ) :
    IsScalarTower ℂ (RadialIncidentSpan k N →L[ℂ] RadialIncidentSpan k N)
      (RadialIncidentSpan k N →L[ℂ] RadialIncidentSpan k N) :=
  ⟨fun r f g => by apply ContinuousLinearMap.ext; intro x; rfl⟩

local instance incidentCStar (k N : ℕ) :
    CStarAlgebra (RadialIncidentSpan k N →L[ℂ] RadialIncidentSpan k N) := inferInstance

local instance incidentComplexCFC (k N : ℕ) :
    ContinuousFunctionalCalculus ℂ (RadialIncidentSpan k N →L[ℂ] RadialIncidentSpan k N)
      IsStarNormal := IsStarNormal.instContinuousFunctionalCalculus

local instance incidentNonUnitalComplexCFC (k N : ℕ) :
    NonUnitalClosedEmbeddingContinuousFunctionalCalculus ℂ
      (RadialIncidentSpan k N →L[ℂ] RadialIncidentSpan k N) IsStarNormal :=
  IsStarNormal.instNonUnitalContinuousFunctionalCalculus

local instance incidentNonUnitalRealCFC (k N : ℕ) :
    NonUnitalContinuousFunctionalCalculus ℝ
      (RadialIncidentSpan k N →L[ℂ] RadialIncidentSpan k N) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance incidentOrder (k N : ℕ) :
    PartialOrder (RadialIncidentSpan k N →L[ℂ] RadialIncidentSpan k N) :=
  ContinuousLinearMap.instLoewnerPartialOrder

local instance incidentStarOrder (k N : ℕ) :
    StarOrderedRing (RadialIncidentSpan k N →L[ℂ] RadialIncidentSpan k N) :=
  ContinuousLinearMap.instStarOrderedRing

local instance incidentNonnegSpectrum (k N : ℕ) :
    NonnegSpectrumClass ℝ (RadialIncidentSpan k N →L[ℂ] RadialIncidentSpan k N) where
  quasispectrum_nonneg_of_nonneg f hf :=
    QuasispectrumRestricts.nnreal_iff.mp <| sub_zero f ▸
      ((ContinuousLinearMap.nonneg_iff_isPositive f).mp hf).spectrumRestricts

/-- Original incident identity minus the adjoint square of the actual return. -/
def radialReturnEnergyDefect (k N : ℕ) :
    RadialIncidentSpan k N →L[ℂ] RadialIncidentSpan k N :=
  1 - (radialReturnTransfer k N).adjoint.comp (radialReturnTransfer k N)

/-- The source defect is self-adjoint before any assertion about its sign. -/
theorem radialReturnEnergyDefect_selfAdjoint (k N : ℕ) :
    IsSelfAdjoint (radialReturnEnergyDefect k N) := by
  change (1 - (radialReturnTransfer k N).adjoint.comp (radialReturnTransfer k N)).adjoint = _
  rw [map_sub, ContinuousLinearMap.adjoint_one, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]
  rfl


/-- Full polarized identity on the unchanged incident Hilbert space. -/
theorem radialReturnEnergyDefect_pairing (k N : ℕ) (x y : RadialIncidentSpan k N) :
    inner ℂ x (radialReturnEnergyDefect k N y) =
      inner ℂ x y - inner ℂ (radialReturnTransfer k N x) (radialReturnTransfer k N y) := by
  simp [radialReturnEnergyDefect,
    ContinuousLinearMap.adjoint_inner_right]

/-- Contractivity is sufficient for positivity of the actual source defect. -/
theorem radialReturnEnergyDefect_nonneg (k N : ℕ)
    (hcontract : ‖radialReturnTransfer k N‖ ≤ 1) :
    0 ≤ radialReturnEnergyDefect k N := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro x
  have hx : ‖radialReturnTransfer k N x‖ ≤ ‖x‖ := by
    calc
      _ ≤ ‖radialReturnTransfer k N‖ * ‖x‖ := (radialReturnTransfer k N).le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hcontract (norm_nonneg x)
      _ = _ := one_mul _
  have he := radialReturnEnergyDefect_pairing k N x x
  have hs := (radialReturnEnergyDefect_selfAdjoint k N).isSymmetric x x
  have he' := hs.trans he
  have heq : inner ℂ (radialReturnEnergyDefect k N x) x =
      ((‖x‖ ^ 2 - ‖radialReturnTransfer k N x‖ ^ 2 : ℝ) : ℂ) := by
    calc
      _ = inner ℂ x x - inner ℂ (radialReturnTransfer k N x) (radialReturnTransfer k N x) := he'
      _ = _ := by
        rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (E := RadialIncidentSpan k N) x,
          inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (E := CanonicalCompletedNativeChiralCauchyCarrier) (radialReturnTransfer k N x)]
        push_cast
        rfl
  rw [heq]
  exact ⟨rfl, sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hx)⟩

/-- Positive square-root channel, included back into the original physical L2.
Its Gram law below requires the independently checked contraction bound. -/
def radialReturnEnergyPort (k N : ℕ) :
    RadialIncidentSpan k N →L[ℂ] CanonicalCompletedNativeChiralCauchyCarrier :=
  ((radialIncidentSynthesis k N).range.subtypeL :
    RadialIncidentSpan k N →L[ℂ] CanonicalCompletedNativeChiralCauchyCarrier).comp
    (CFC.sqrt (radialReturnEnergyDefect k N))

/-- The entire source defect, with independent inputs and all crossings,
is represented by the positive energy channel under actual contractivity. -/
theorem radialReturnEnergyPort_inner (k N : ℕ)
    (hcontract : ‖radialReturnTransfer k N‖ ≤ 1) (x y : RadialIncidentSpan k N) :
    inner ℂ (radialReturnEnergyPort k N x) (radialReturnEnergyPort k N y) =
      inner ℂ x y - inner ℂ (radialReturnTransfer k N x) (radialReturnTransfer k N y) := by
  have hs : IsSelfAdjoint (CFC.sqrt (radialReturnEnergyDefect k N)) :=
    (CFC.sqrt_nonneg _).isSelfAdjoint
  have hsq := CFC.sqrt_mul_sqrt_self (radialReturnEnergyDefect k N)
    (radialReturnEnergyDefect_nonneg k N hcontract)
  change inner ℂ (CFC.sqrt (radialReturnEnergyDefect k N) x)
    (CFC.sqrt (radialReturnEnergyDefect k N) y) = _
  have hsym : inner ℂ (CFC.sqrt (radialReturnEnergyDefect k N) x)
      (CFC.sqrt (radialReturnEnergyDefect k N) y) =
      inner ℂ x (CFC.sqrt (radialReturnEnergyDefect k N)
        (CFC.sqrt (radialReturnEnergyDefect k N) y)) := hs.isSymmetric _ _
  rw [hsym]
  change inner ℂ x ((CFC.sqrt (radialReturnEnergyDefect k N) *
    CFC.sqrt (radialReturnEnergyDefect k N)) y) = _
  rw [hsq]
  exact radialReturnEnergyDefect_pairing k N x y

/-- The exact polarized completed source balance is the Gram of this port.
The source precedes the return, defect, and positive square root. -/
theorem radialReturnEnergyPort_source_gram (k N : ℕ)
    (hcontract : ‖radialReturnTransfer k N‖ ≤ 1)
    (c d : Fin N → ℂ)
    (hpositive : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    inner ℂ (radialReturnEnergyPort k N (radialIncidentVector k N c))
      (radialReturnEnergyPort k N (radialIncidentVector k N d)) =
      polarizedSourceBalance k c d 1 1 := by
  rw [radialReturnEnergyPort_inner k N hcontract]
  exact radialReturnTransfer_polarized_balance k N c d hpositive

/-- Exact diagonal storage, without target-moment normalization. -/
theorem radialReturnEnergyPort_norm_sq (k N : ℕ)
    (hcontract : ‖radialReturnTransfer k N‖ ≤ 1) (c : Fin N → ℂ) :
    ‖radialReturnEnergyPort k N (radialIncidentVector k N c)‖ ^ 2 =
      (storage k c 1).re := by
  have h := radialReturnEnergyPort_inner k N hcontract
    (radialIncidentVector k N c) (radialIncidentVector k N c)
  have hr := congrArg Complex.re h
  simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow,
    storage_one_eq_finiteTransfer_energy] using hr

/-- Seven original sources: positivity is supplied by the proved complete-source
estimate, not a hypothesis on moments or on the requested Gram. -/
theorem radialReturnEnergyPort_seven_eventually_gram :
    ∀ᶠ k : ℕ in atTop, ∀ c d : Fin 7 → ℂ,
      inner ℂ (radialReturnEnergyPort k 7 (radialIncidentVector k 7 c))
        (radialReturnEnergyPort k 7 (radialIncidentVector k 7 d)) =
        polarizedSourceBalance k c d 1 1 := by
  filter_upwards [radialReturnTransfer_seven_eventually_norm_le_one,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 7] with k hk hreg
  intro c d
  exact radialReturnEnergyPort_source_gram k 7 hk c d (fun i => (hreg i).2.2)

/-- The seven-source energy port loses no nonzero original incident source. -/
theorem radialReturnEnergyPort_seven_eventually_pos :
    ∀ᶠ k : ℕ in atTop, ∀ c : Fin 7 → ℂ, c ≠ 0 →
      0 < ‖radialReturnEnergyPort k 7 (radialIncidentVector k 7 c)‖ ^ 2 := by
  filter_upwards [radialReturnTransfer_seven_eventually_norm_le_one,
    storage_one_original_sevenSample_eventually_pos] with k hk hp
  intro c hc
  rw [radialReturnEnergyPort_norm_sq k 7 hk]
  exact hp c hc

/-- Coefficients of the OLD factorial-normalized radial difference jet.
They depend on source amplitudes and the grid, never on moments or a Gram. -/
def radialDifferenceSourceCoefficients (k N order : ℕ) (r : Fin N) : ℂ :=
  (((order.factorial : ℂ) * canonicalCompletedC3RadialSecondStep k ^ order)⁻¹) *
    completedGreenForwardWeight order r.val *
    completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k r)

/-- Both actual incident/return syntheses recover the complete signed jet
before the positive energy factor is applied. -/
theorem radialDifferenceSource_pair (k N order : ℕ) (ho : order < N) :
    (radialIncidentSynthesis k N (radialDifferenceSourceCoefficients k N order),
      radialReturnedSynthesis k N (radialDifferenceSourceCoefficients k N order)) =
      projectiveChiralDifferenceJet k order := by
  have hsum : (∑ r ∈ Finset.range (order+1), completedGreenForwardWeight order r •
      canonicalCompletedNativeRadialProjectiveChiralState k r) =
      ∑ r : Fin N, completedGreenForwardWeight order r.val •
        canonicalCompletedNativeRadialProjectiveChiralState k r := by
    rw [Fin.sum_univ_eq_sum_range
      (fun r : ℕ => completedGreenForwardWeight order r •
        canonicalCompletedNativeRadialProjectiveChiralState k r) N]
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro r _ hr
    have hlt : order < r := by
      have hn : ¬ r < order+1 := by simpa only [Finset.mem_range] using hr
      omega
    simp [completedGreenForwardWeight, Nat.choose_eq_zero_of_lt hlt]
  have he : projectiveChiralDifferenceJet k order =
      ∑ r : Fin N, radialDifferenceSourceCoefficients k N order r •
        canonicalCompletedNativeRadialChiralDefectState k r := by
    unfold projectiveChiralDifferenceJet
    rw [hsum]
    simp only [canonicalCompletedNativeRadialProjectiveChiralState,
      radialDifferenceSourceCoefficients, Finset.smul_sum, smul_smul, mul_assoc]
  rw [he]
  apply Prod.ext
  · exact (map_sum (AddMonoidHom.fst _ _)
      (fun r : Fin N => radialDifferenceSourceCoefficients k N order r •
        canonicalCompletedNativeRadialChiralDefectState k r) Finset.univ).symm
  · exact (map_sum (AddMonoidHom.snd _ _)
      (fun r : Fin N => radialDifferenceSourceCoefficients k N order r •
        canonicalCompletedNativeRadialChiralDefectState k r) Finset.univ).symm

/-- Positive physical jet port. The fixed 1/sqrt(2) implements the ALREADY
EXISTING 1/2 in canonicalCompletedNativeProjectiveChiralForm. -/
def radialReturnEnergyJet (k N : ℕ) (a : Fin N) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  (Real.sqrt 2 : ℂ)⁻¹ • radialReturnEnergyPort k N
    (radialIncidentVector k N (radialDifferenceSourceCoefficients k N a.val))

/-- Under source contractivity, the positive jet Gram equals the ORIGINAL
signed projective pairing, including independent orders and every crossing. -/
theorem radialReturnEnergyJet_gram (k N : ℕ)
    (hcontract : ‖radialReturnTransfer k N‖ ≤ 1) (a b : Fin N) :
    inner ℂ (radialReturnEnergyJet k N a) (radialReturnEnergyJet k N b) =
      canonicalCompletedNativeProjectiveChiralForm
        (projectiveChiralDifferenceJet k a.val) (projectiveChiralDifferenceJet k b.val) := by
  have hscale : conj ((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rfl
  simp only [radialReturnEnergyJet, inner_smul_left, inner_smul_right,
    ← mul_assoc]
  rw [mul_comm ((Real.sqrt 2 : ℂ)⁻¹) (conj ((Real.sqrt 2 : ℂ)⁻¹)), hscale]
  rw [radialReturnEnergyPort_inner k N hcontract,
    radialReturnTransfer_exact, radialReturnTransfer_exact]
  rw [← radialDifferenceSource_pair k N a.val a.isLt,
    ← radialDifferenceSource_pair k N b.val b.isLt]
  rfl

/-- SEVEN sources: the full positive port Gram is valid eventually without
assuming native positivity or a desired moment identity. -/
theorem radialReturnEnergyJet_seven_eventually_gram :
    ∀ᶠ k : ℕ in atTop, ∀ a b : Fin 7,
      inner ℂ (radialReturnEnergyJet k 7 a) (radialReturnEnergyJet k 7 b) =
        canonicalCompletedNativeProjectiveChiralForm
          (projectiveChiralDifferenceJet k a.val) (projectiveChiralDifferenceJet k b.val) := by
  filter_upwards [radialReturnTransfer_seven_eventually_norm_le_one] with k hk
  intro a b
  exact radialReturnEnergyJet_gram k 7 hk a b

/-- Concrete positive energy vectors now reproduce ALL entries of the
seven-order canonical coefficient block in the radial limit. This asserts
Gram convergence, not convergence of the vectors or a global kernel. -/
theorem radialReturnEnergyJet_seven_inner_tendsto (a b : Fin 7) :
    Tendsto (fun k => inner ℂ (radialReturnEnergyJet k 7 a) (radialReturnEnergyJet k 7 b))
      atTop (nhds (polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment a.val b.val)) := by
  apply (projectiveChiralDifferenceJet_pairing_tendsto_coefficient a.val b.val).congr'
  filter_upwards [radialReturnEnergyJet_seven_eventually_gram] with k hk
  exact (hk a b).symm

/-- The new source-derived port passes the zeroth native mass test IN THE
LIMIT, rather than inheriting the value port's incompatible mass 1/2. -/
theorem radialReturnEnergyJet_seven_zero_norm_sq_tendsto :
    Tendsto (fun k => ‖radialReturnEnergyJet k 7 0‖ ^ 2)
      atTop (nhds (canonicalCompletedNativeLogDerivativeMoment 0)) := by
  have h := radialReturnEnergyJet_seven_inner_tendsto 0 0
  have hr := Complex.continuous_re.continuousAt.tendsto.comp h
  simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow,
    polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient, Function.comp_def] using hr

/-- The completed geometric correction is exactly the difference between
camera energy and HALF of the actual positive port energy. -/
theorem radialReturnEnergyPort_camera_correction (k N : ℕ)
    (hcontract : ‖radialReturnTransfer k N‖ ≤ 1) (c : Fin N → ℂ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
      CPFormal.Analytic.Cp.genuineCriticalStrip)
    (hpositive : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    2 * (coisometricFourChannelBalance k c c 1 1 (fun i => (hstrip i).1)).im +
      ‖radialReturnEnergyPort k N (radialIncidentVector k N c)‖ ^ 2 =
        2 * ‖coisometricSourceSynthesis k c 1 (fun i => (hstrip i).1)‖ ^ 2 := by
  rw [radialReturnEnergyPort_norm_sq k N hcontract,
    storage_re_eq_coisometricEnergy_sub_fourChannelBalance 0 k c 1 hstrip hpositive]
  ring


/-- One complete radial source, with its unchanged projective amplitude. -/
def radialSampleSourceCoefficients (k N : ℕ) (i : Fin N) : Fin N → ℂ :=
  Pi.single i (completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k i))

/-- Actual incident and return of this sample are the old projective pair. -/
theorem radialSampleSource_pair (k N : ℕ) (i : Fin N) :
    (radialIncidentSynthesis k N (radialSampleSourceCoefficients k N i),
      radialReturnedSynthesis k N (radialSampleSourceCoefficients k N i)) =
      canonicalCompletedNativeRadialProjectiveChiralState k i := by
  classical
  apply Prod.ext <;>
    simp [radialSampleSourceCoefficients, radialIncidentSynthesis, radialReturnedSynthesis,
      canonicalCompletedNativeRadialProjectiveChiralState,
      canonicalCompletedNativeRadialChiralDefectState]

/-- Source-derived positive port for a point on the original radial grid. -/
def radialReturnSampleEnergyPort (k N : ℕ) (i : Fin N) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  (Real.sqrt 2 : ℂ)⁻¹ • radialReturnEnergyPort k N
    (radialIncidentVector k N (radialSampleSourceCoefficients k N i))

/-- The finite positive port realizes the ORIGINAL canonical radial kernel,
not a fitted matrix. The hypothesis is on the actual source return. -/
theorem radialReturnSampleEnergyPort_inner (k N : ℕ)
    (hcontract : ‖radialReturnTransfer k N‖ ≤ 1)
    (hregular : ∀ i : Fin N,
      canonicalCompletedC3RadialTiltPoint k i ∈ completedNativeHeightDomain ∧
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (i j : Fin N) :
    inner ℂ (radialReturnSampleEnergyPort k N i) (radialReturnSampleEnergyPort k N j) =
      canonicalCompletedNativeRadialDslopeSampleMatrix k N i j := by
  have hscale : conj ((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rfl
  simp only [radialReturnSampleEnergyPort, inner_smul_left, inner_smul_right, ← mul_assoc]
  rw [mul_comm ((Real.sqrt 2 : ℂ)⁻¹) (conj ((Real.sqrt 2 : ℂ)⁻¹)), hscale,
    radialReturnEnergyPort_inner k N hcontract,
    radialReturnTransfer_exact, radialReturnTransfer_exact]
  rw [← canonicalCompletedNativeRadialProjectiveChiralForm_eq_dslope k N hregular i j,
    ← radialSampleSource_pair k N i, ← radialSampleSource_pair k N j]
  rfl

/-- Seven-source realization of the exact two-variable kernel on the radial
grid, with all independent sample pairings, and no positivity premise. -/
theorem radialReturnSampleEnergyPort_seven_eventually_kernel :
    ∀ᶠ k : ℕ in atTop, ∀ i j : Fin 7,
      inner ℂ (radialReturnSampleEnergyPort k 7 i) (radialReturnSampleEnergyPort k 7 j) =
        canonicalCompletedNativeRadialDslopeSampleMatrix k 7 i j := by
  filter_upwards [radialReturnTransfer_seven_eventually_norm_le_one,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 7] with k hk hreg
  intro i j
  exact radialReturnSampleEnergyPort_inner k 7 hk hreg i j

/-- The arbitrary finite-order statement remains explicit about its missing
return estimate. No new all-order positivity certificate is postulated. -/
theorem radialReturnEnergyJet_inner_tendsto_of_eventually_contractive (N : ℕ)
    (hcontract : ∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k N‖ ≤ 1) (a b : Fin N) :
    Tendsto (fun k => inner ℂ (radialReturnEnergyJet k N a) (radialReturnEnergyJet k N b))
      atTop (nhds (polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment a.val b.val)) := by
  apply (projectiveChiralDifferenceJet_pairing_tendsto_coefficient a.val b.val).congr'
  filter_upwards [hcontract] with k hk
  exact (radialReturnEnergyJet_gram k N hk a b).symm

/-- Even coefficients in the realized seven-source section: four even jets. -/
theorem radialReturnEnergyJet_seven_even_inner_tendsto (i j : Fin 4) :
    Tendsto (fun k => inner ℂ
      (radialReturnEnergyJet k 7 ⟨2*i.val, by omega⟩)
      (radialReturnEnergyJet k 7 ⟨2*j.val, by omega⟩)) atTop
      (nhds (canonicalCompletedNativeLogDerivativeMoment (i.val+j.val) : ℂ)) := by
  simpa only [polarizedGreenMomentCoefficient_even_even] using
    radialReturnEnergyJet_seven_inner_tendsto
      ⟨2*i.val, by omega⟩ ⟨2*j.val, by omega⟩

/-- Odd coefficients in the realized section: three odd jets. -/
theorem radialReturnEnergyJet_seven_odd_inner_tendsto (i j : Fin 3) :
    Tendsto (fun k => inner ℂ
      (radialReturnEnergyJet k 7 ⟨2*i.val+1, by omega⟩)
      (radialReturnEnergyJet k 7 ⟨2*j.val+1, by omega⟩)) atTop
      (nhds (canonicalCompletedNativeLogDerivativeMoment (i.val+j.val+1) : ℂ)) := by
  simpa only [polarizedGreenMomentCoefficient_odd_odd] using
    radialReturnEnergyJet_seven_inner_tendsto
      ⟨2*i.val+1, by omega⟩ ⟨2*j.val+1, by omega⟩

/-- Mixed parity crosses are retained at finite step and tend to zero. -/
theorem radialReturnEnergyJet_seven_even_odd_inner_tendsto (i : Fin 4) (j : Fin 3) :
    Tendsto (fun k => inner ℂ
      (radialReturnEnergyJet k 7 ⟨2*i.val, by omega⟩)
      (radialReturnEnergyJet k 7 ⟨2*j.val+1, by omega⟩)) atTop (nhds (0 : ℂ)) := by
  simpa only [polarizedGreenMomentCoefficient_even_odd] using
    radialReturnEnergyJet_seven_inner_tendsto
      ⟨2*i.val, by omega⟩ ⟨2*j.val+1, by omega⟩


end
end CarrySelfAdjointOperator.ChiralReturn
