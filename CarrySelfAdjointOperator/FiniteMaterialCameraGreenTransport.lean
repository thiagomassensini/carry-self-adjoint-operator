import CarrySelfAdjointOperator.FiniteMultibaseMaterialBracketTransport
import CarrySelfAdjointOperator.GreenParsevalMaterialLogOperator
import Mathlib.Analysis.PSeries

/-! Finite literal material vectors in the existing Green State and its
canonical Parseval analysis. The map is the finite nodal inclusion; the
unbounded operator's domain is checked, not replaced by a new clock. This
does not identify nodal vectors with the analytic chiral completed source. -/

noncomputable section
open scoped BigOperators InnerProduct lp Topology
namespace CarrySelfAdjointOperator.MaterialCameraJets
open CPFormal.Analytic.Cp FiniteClockJets GreenFrame.Concrete
open GreenStateMaterialLog GreenParsevalMaterialLog

/-- Positive-material finite inclusion in the existing infinite Green State. -/
def finiteGreenMaterialEmbedding (N : ℕ) : FiniteRealSpectralHilbert N →ₗ[ℂ] State where
  toFun x := ∑ n : Fin N, x n • greenMaterialBasisVector (natEquivPNat n.val)
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, mul_smul]

private theorem finiteGreenBasis_inner {N : ℕ} (i j : Fin N) :
    inner ℂ (greenMaterialBasisVector (natEquivPNat i.val))
      (greenMaterialBasisVector (natEquivPNat j.val)) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simp [greenMaterialBasisVector]
  · have hn : natEquivPNat i.val ≠ natEquivPNat j.val := by
      intro he
      exact h (Fin.ext (natEquivPNat.injective he))
    simp [greenMaterialBasisVector, lp.inner_single_left, lp.single_apply, hn, h]

/-- No metric adjustment: the finite nodal inclusion is isometric. -/
theorem finiteGreenMaterialEmbedding_inner (N : ℕ) (x y : FiniteRealSpectralHilbert N) :
    inner ℂ (finiteGreenMaterialEmbedding N x) (finiteGreenMaterialEmbedding N y) =
      inner ℂ x y := by
  simp only [finiteGreenMaterialEmbedding, LinearMap.coe_mk, AddHom.coe_mk,
    inner_sum, sum_inner, inner_smul_left, inner_smul_right, finiteGreenBasis_inner]
  rw [PiLp.inner_apply]
  simp [RCLike.inner_apply, mul_comm]

/-- Every finite image lies in the genuine logarithmic domain. -/
theorem finiteGreenMaterialEmbedding_mem_domain (N : ℕ) (x : FiniteRealSpectralHilbert N) :
    finiteGreenMaterialEmbedding N x ∈ greenStateMaterialLogGenerator.domain := by
  change (∑ n : Fin N, x n • greenMaterialBasisVector (natEquivPNat n.val)) ∈ _
  apply Submodule.sum_mem
  intro n hn
  exact Submodule.smul_mem _ _ (greenMaterialBasisVector_mem_domain _)

/-- Vector intertwining of the unchanged finite and infinite material clocks. -/
theorem finiteGreenMaterialEmbedding_clock (N : ℕ) (x : FiniteRealSpectralHilbert N) :
    greenStateMaterialLogGenerator
      ⟨finiteGreenMaterialEmbedding N x, finiteGreenMaterialEmbedding_mem_domain N x⟩ =
        finiteGreenMaterialEmbedding N (finiteMaterialClock N x) := by
  ext m
  rw [greenStateMaterialLogGenerator_apply]
  simp only [finiteGreenMaterialEmbedding, LinearMap.coe_mk, AddHom.coe_mk,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    finiteRealSpectralGenerator_apply, greenMaterialBasisVector, lp.single_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases he : m = natEquivPNat n.val
  · subst m
    simp [finiteRealSpectralFrequency]
  · simp [he]

/-- Fixed Green Parseval promotion of the same finite material state. -/
def finiteParsevalMaterialEmbedding (N : ℕ) :
    FiniteRealSpectralHilbert N →ₗ[ℂ] ConcreteAnalysisSpace :=
  greenParsevalAnalysis.toLinearMap.comp (finiteGreenMaterialEmbedding N)

theorem finiteParsevalMaterialEmbedding_inner (N : ℕ) (x y : FiniteRealSpectralHilbert N) :
    inner ℂ (finiteParsevalMaterialEmbedding N x) (finiteParsevalMaterialEmbedding N y) =
      inner ℂ x y := by
  change inner ℂ (greenParsevalAnalysis (finiteGreenMaterialEmbedding N x))
    (greenParsevalAnalysis (finiteGreenMaterialEmbedding N y)) = _
  exact ((ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self greenParsevalAnalysis).mpr
    greenParsevalAnalysis_gram_identity _ _).trans (finiteGreenMaterialEmbedding_inner N x y)

theorem finiteParsevalMaterialEmbedding_mem_domain (N : ℕ) (x : FiniteRealSpectralHilbert N) :
    finiteParsevalMaterialEmbedding N x ∈ greenParsevalMaterialLogOperator.domain :=
  (greenParsevalMaterialLogOperator_P_mem_domain_iff _).mpr
    (finiteGreenMaterialEmbedding_mem_domain N x)

theorem finiteParsevalMaterialEmbedding_clock (N : ℕ) (x : FiniteRealSpectralHilbert N) :
    greenParsevalMaterialLogOperator
      ⟨finiteParsevalMaterialEmbedding N x, finiteParsevalMaterialEmbedding_mem_domain N x⟩ =
        finiteParsevalMaterialEmbedding N (finiteMaterialClock N x) := by
  change greenParsevalMaterialLogOperator
    ⟨greenParsevalAnalysis (finiteGreenMaterialEmbedding N x), _⟩ = _
  rw [greenParsevalMaterialLogOperator_intertwining _ (finiteGreenMaterialEmbedding_mem_domain N x),
    finiteGreenMaterialEmbedding_clock]
  rfl

/-- All orders lie in the real domain and transport their next jet as vectors. -/
theorem finiteParsevalMaterialEmbedding_allOrder_step (N r : ℕ)
    (x : FiniteRealSpectralHilbert N) :
    greenParsevalMaterialLogOperator
      ⟨finiteParsevalMaterialEmbedding N (materialJet r x),
        finiteParsevalMaterialEmbedding_mem_domain N (materialJet r x)⟩ =
      finiteParsevalMaterialEmbedding N (materialJet (r + 1) x) := by
  rw [finiteParsevalMaterialEmbedding_clock]
  simp [materialJet, pow_succ', Module.End.mul_apply]

/-- Mixed-order physical pairings survive the actual Parseval promotion. -/
theorem finiteParsevalMaterialEmbedding_jet_pairing (N r s : ℕ)
    (x y : FiniteRealSpectralHilbert N) :
    inner ℂ (finiteParsevalMaterialEmbedding N (materialJet r x))
      (finiteParsevalMaterialEmbedding N (materialJet s y)) =
        inner ℂ x (materialJet (r + s) y) := by
  rw [finiteParsevalMaterialEmbedding_inner, materialJet_pairing]

/-- The seed and every geometric center survive Parseval promotion as vectors. -/
theorem finiteParsevalMaterialEmbedding_camera_jet_synthesis (N b M r : ℕ)
    (x : FiniteRealSpectralHilbert N) :
    finiteParsevalMaterialEmbedding N (materialJet r (cameraMaterialAction b M x)) =
      finiteParsevalMaterialEmbedding N (stencilMaterialAction (materialJet r x) (NativeCarrySpectralWeyl.Camera.FiniteBridge.seedStencil b)) +
        ∑ j ∈ Finset.range M, finiteParsevalMaterialEmbedding N
          (stencilMaterialAction (materialJet r x) (NativeCarrySpectralWeyl.Camera.FiniteBridge.centerStencil b j)) := by
  rw [cameraMaterialJet_eq_seed_add_centerSum, map_add, map_sum]

private theorem historicalInitialState_coordinate_norm_sq {N : ℕ} (n : Fin N) :
    ‖historicalInitialState N n‖^2 = ((n.val+1 : ℕ) : ℝ)⁻¹ := by
  simp [historicalInitialState, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow]
  exact Real.sq_sqrt (by positivity)

/-- The unchanged critical amplitude has exactly harmonic nodal energy. -/
theorem finiteParsevalMaterialEmbedding_critical_energy (N : ℕ) :
    ‖finiteParsevalMaterialEmbedding N (historicalInitialState N)‖^2 =
      ∑ j ∈ Finset.range N, ((j+1 : ℕ) : ℝ)⁻¹ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), finiteParsevalMaterialEmbedding_inner,
    ← norm_sq_eq_re_inner (𝕜 := ℂ), EuclideanSpace.norm_sq_eq]
  simp_rw [historicalInitialState_coordinate_norm_sq]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => ((j+1 : ℕ) : ℝ)⁻¹) N

/-- Lossless nodal transport does not remove the critical energy divergence. -/
theorem finiteParsevalMaterialEmbedding_critical_energy_tendsto :
    Filter.Tendsto
      (fun N => ‖finiteParsevalMaterialEmbedding N (historicalInitialState N)‖^2)
      Filter.atTop Filter.atTop := by
  simp_rw [finiteParsevalMaterialEmbedding_critical_energy]
  simpa only [Nat.cast_add, Nat.cast_one, one_div] using
    Real.tendsto_sum_range_one_div_nat_succ_atTop

/-- This actual lossless critical nodal family has no ambient Hilbert limit. -/
theorem finiteParsevalMaterialEmbedding_critical_no_limit :
    ¬ ∃ z : ConcreteAnalysisSpace,
      Filter.Tendsto (fun N => finiteParsevalMaterialEmbedding N (historicalInitialState N))
        Filter.atTop (nhds z) := by
  rintro ⟨z,hz⟩
  have hn := (continuous_norm.pow 2).tendsto z |>.comp hz
  exact not_tendsto_nhds_of_tendsto_atTop
    finiteParsevalMaterialEmbedding_critical_energy_tendsto (‖z‖^2)
    (by simpa only [Function.comp_def, Pi.pow_apply] using hn)

end CarrySelfAdjointOperator.MaterialCameraJets
