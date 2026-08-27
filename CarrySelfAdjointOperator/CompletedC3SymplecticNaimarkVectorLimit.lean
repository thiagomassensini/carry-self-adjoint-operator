import CarrySelfAdjointOperator.CompletedC3SymplecticNaimarkLimitBridge
import CarrySelfAdjointOperator.RealLinearPMapComplexification
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic

/-!
# Vector completion of the all-cutoff C3 symplectic Naimark states

Every finite C3 leg in `CompletedC3SymplecticNaimarkLimitBridge` was embedded
through one permanent orthonormal camera family.  This file constructs the
corresponding infinite synthesis map and proves that finite complex prefixes
converge in the camera Hilbert space before any Green or scalar readout.

Real and imaginary coordinates remain separate throughout the construction.
The final Naimark limit is obtained only by continuity of the already-defined
Naimark isometry.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace
  RealInnerProductSpace Topology lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-! ## One global synthesis for all complex coordinates -/

/-- Permanent camera coordinate of the real or imaginary quadrature of the
`n`-th complex `l2` coordinate. -/
def completedC3GlobalRealCoordinateNat (j : ℕ × Fin 2) : ℕ :=
  2 * j.1 + j.2.val

theorem completedC3GlobalRealCoordinateNat_injective :
    Function.Injective completedC3GlobalRealCoordinateNat := by
  intro i j hij
  apply Prod.ext
  · dsimp [completedC3GlobalRealCoordinateNat] at hij
    omega
  · apply Fin.ext
    dsimp [completedC3GlobalRealCoordinateNat] at hij
    omega

/-- The permanent camera family, reindexed by complex coordinate and retained
quadrature, is still orthonormal. -/
theorem completedC3GlobalRealCameraVector_orthonormal :
    Orthonormal ℝ (fun j : ℕ × Fin 2 ↦
      completedC3OrthonormalCameraVector
        (completedC3GlobalRealCoordinateNat j)) := by
  simpa [Function.comp_def] using
    completedC3OrthonormalCameraVector_orthonormal.comp
      completedC3GlobalRealCoordinateNat
      completedC3GlobalRealCoordinateNat_injective

/-- Real `l2` coordinates indexed by complex cell and quadrature. -/
abbrev CompletedC3GlobalRealL2 := ℓ²(ℕ × Fin 2, ℝ)

/-- Infinite isometric synthesis of all retained real and imaginary
quadratures in the one global camera Hilbert space. -/
theorem completedC3GlobalCameraCoordinateOrthogonalFamily :
    OrthogonalFamily ℝ (fun _ : ℕ × Fin 2 ↦ ℝ)
      (fun j ↦ LinearIsometry.toSpanSingleton ℝ CameraHilbert
        (completedC3GlobalRealCameraVector_orthonormal.1 j)) :=
  completedC3GlobalRealCameraVector_orthonormal.orthogonalFamily

def completedC3GlobalCameraCoordinateSynthesis :
    CompletedC3GlobalRealL2 →ₗᵢ[ℝ] CameraHilbert :=
  completedC3GlobalCameraCoordinateOrthogonalFamily.linearIsometry

/-- Square summability of the two retained quadratures. -/
theorem summable_completedC3RealifiedL2Coordinate_norm_sq
    (x : CarryVerticalL2) :
    Summable (fun j : ℕ × Fin 2 ↦
      ‖![(x j.1).re, (x j.1).im] j.2‖ ^ (2 : ℝ)) := by
  rw [summable_prod_of_nonneg (fun _ ↦ by positivity)]
  constructor
  · intro n
    exact (hasSum_fintype _).summable
  · have hx : Summable (fun n : ℕ ↦ ‖x n‖ ^ (2 : ℝ)) :=
      (lp.memℓp x).summable (by norm_num)
    apply hx.congr
    intro n
    rw [tsum_fintype, Fin.sum_univ_two]
    simp [Real.norm_eq_abs, sq]
    simpa [pow_two, Complex.normSq_apply] using Complex.sq_norm (x n)

/-- Real and imaginary coordinates of one complex `l2` state, without an
early real-part projection. -/
def completedC3RealifiedL2CoordinateState (x : CarryVerticalL2) :
    CompletedC3GlobalRealL2 :=
  ⟨fun j ↦ ![(x j.1).re, (x j.1).im] j.2, by
    change Memℓp (fun j : ℕ × Fin 2 ↦
      ![(x j.1).re, (x j.1).im] j.2) 2
    rw [memℓp_gen_iff (by norm_num)]
    simpa using summable_completedC3RealifiedL2Coordinate_norm_sq x⟩

@[simp] theorem completedC3RealifiedL2CoordinateState_apply
    (x : CarryVerticalL2) (j : ℕ × Fin 2) :
    completedC3RealifiedL2CoordinateState x j =
      ![(x j.1).re, (x j.1).im] j.2 :=
  rfl

/-- The two retained quadratures have exactly the original complex `l2`
energy. -/
theorem completedC3RealifiedL2CoordinateState_norm
    (x : CarryVerticalL2) :
    ‖completedC3RealifiedL2CoordinateState x‖ = ‖x‖ := by
  have htarget := lp.norm_rpow_eq_tsum (by norm_num)
    (completedC3RealifiedL2CoordinateState x)
  have hsource := lp.norm_rpow_eq_tsum (by norm_num) x
  norm_num at htarget hsource
  have hsquare :
      ‖completedC3RealifiedL2CoordinateState x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [htarget, hsource]
    have hcoordinate : Summable (fun j : ℕ × Fin 2 ↦
        ![(x j.1).re, (x j.1).im] j.2 ^ (2 : ℕ)) :=
      (summable_completedC3RealifiedL2Coordinate_norm_sq x).congr
        (fun j ↦ by simp [Real.norm_eq_abs, sq])
    rw [hcoordinate.tsum_prod]
    apply tsum_congr
    intro n
    rw [tsum_fintype, Fin.sum_univ_two]
    simp [sq]
    simpa [pow_two, Complex.normSq_apply] using (Complex.sq_norm (x n)).symm
  nlinarith [norm_nonneg (completedC3RealifiedL2CoordinateState x), norm_nonneg x]

/-! ## Isometric complex-leg completion -/

/-- Real-linear realification of an entire complex `l2` leg. -/
def completedC3RealifiedL2CoordinateLinearMap :
    CarryVerticalL2 →ₗ[ℝ] CompletedC3GlobalRealL2 where
  toFun := completedC3RealifiedL2CoordinateState
  map_add' x y := by
    apply lp.ext
    funext j
    rcases j with ⟨n, k⟩
    fin_cases k <;> simp [completedC3RealifiedL2CoordinateState]
  map_smul' r x := by
    apply lp.ext
    funext j
    rcases j with ⟨n, k⟩
    fin_cases k <;> simp [completedC3RealifiedL2CoordinateState,
      Complex.real_smul]

/-- No energy is lost by retaining the two quadratures separately. -/
def completedC3RealifiedL2CoordinateIsometry :
    CarryVerticalL2 →ₗᵢ[ℝ] CompletedC3GlobalRealL2 where
  toLinearMap := completedC3RealifiedL2CoordinateLinearMap
  norm_map' := completedC3RealifiedL2CoordinateState_norm

@[simp] theorem completedC3RealifiedL2CoordinateIsometry_apply
    (x : CarryVerticalL2) :
    completedC3RealifiedL2CoordinateIsometry x =
      completedC3RealifiedL2CoordinateState x :=
  rfl

/-- Completed camera realization of one complex `l2` leg. -/
def completedC3GlobalLegCameraIsometry :
    CarryVerticalL2 →ₗᵢ[ℝ] CameraHilbert :=
  completedC3GlobalCameraCoordinateSynthesis.comp
    completedC3RealifiedL2CoordinateIsometry

/-- One complex coordinate is synthesized as its two permanent orthogonal
camera quadratures. -/
theorem completedC3GlobalLegCameraIsometry_single
    (n : ℕ) (z : ℂ) :
    completedC3GlobalLegCameraIsometry (lp.single 2 n z) =
      z.re • completedC3OrthonormalCameraVector (2 * n) +
        z.im • completedC3OrthonormalCameraVector (2 * n + 1) := by
  have hcoordinate :
      completedC3RealifiedL2CoordinateState (lp.single 2 n z) =
        lp.single 2 (n, (0 : Fin 2)) z.re +
          lp.single 2 (n, (1 : Fin 2)) z.im := by
    apply lp.ext
    funext j
    rcases j with ⟨m, k⟩
    fin_cases k <;> by_cases hmn : m = n <;>
      simp [completedC3RealifiedL2CoordinateState, hmn]
  change completedC3GlobalCameraCoordinateSynthesis
      (completedC3RealifiedL2CoordinateState (lp.single 2 n z)) = _
  rw [hcoordinate, map_add]
  change
    completedC3GlobalCameraCoordinateOrthogonalFamily.linearIsometry
          (lp.single 2 (n, (0 : Fin 2)) z.re) +
        completedC3GlobalCameraCoordinateOrthogonalFamily.linearIsometry
          (lp.single 2 (n, (1 : Fin 2)) z.im) = _
  rw [
    completedC3GlobalCameraCoordinateOrthogonalFamily.linearIsometry_apply_single,
    completedC3GlobalCameraCoordinateOrthogonalFamily.linearIsometry_apply_single]
  simp [completedC3GlobalRealCoordinateNat]

/-- Extend one finite complex C3 leg by zero to the common complex `l2`
carrier. -/
def finiteC3LegL2Extension (M : ℕ)
    (x : NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace M) :
    CarryVerticalL2 :=
  ∑ n : Fin M, lp.single 2 n.val (x n)

@[simp] theorem finiteC3LegL2Extension_apply
    (M : ℕ)
    (x : NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace M)
    (n : ℕ) :
    finiteC3LegL2Extension M x n =
      if h : n < M then x ⟨n, h⟩ else 0 := by
  classical
  unfold finiteC3LegL2Extension
  simp only [lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply]
  by_cases hn : n < M
  · rw [Finset.sum_eq_single ⟨n, hn⟩]
    · simp [hn]
    · intro b _ hne
      rw [Pi.single_eq_of_ne]
      intro hval
      apply hne
      apply Fin.ext
      exact hval.symm
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [hn]
    · intro b _
      rw [Pi.single_eq_of_ne]
      intro hval
      apply hn
      exact hval ▸ b.isLt

/-- The global synthesis of a zero-extended finite leg is literally its
existing all-cutoff camera embedding. -/
theorem completedC3GlobalLegCameraIsometry_finiteExtension
    (M : ℕ)
    (x : NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace M) :
    completedC3GlobalLegCameraIsometry (finiteC3LegL2Extension M x) =
      finiteC3LegCameraIsometry M x := by
  rw [finiteC3LegL2Extension, map_sum]
  simp_rw [completedC3GlobalLegCameraIsometry_single]
  change
    (∑ n : Fin M, (
      (x n).re • completedC3OrthonormalCameraVector (2 * n.val) +
        (x n).im • completedC3OrthonormalCameraVector (2 * n.val + 1))) =
      ∑ j : FiniteC3RealCoordinate M,
        ![(x j.1).re, (x j.1).im] j.2 •
          completedC3OrthonormalCameraVector
            (finiteC3RealCoordinateNat j)
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro n _
  rw [Fin.sum_univ_two]
  rfl

/-- Zero extension commutes with the complex quarter turn before the real
camera synthesis is applied. -/
theorem finiteC3LegL2Extension_I_smul
    (M : ℕ)
    (x : NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace M) :
    finiteC3LegL2Extension M (Complex.I • x) =
      Complex.I • finiteC3LegL2Extension M x := by
  apply lp.ext
  funext n
  rw [finiteC3LegL2Extension_apply]
  change (if h : n < M then (Complex.I • x) ⟨n, h⟩ else 0) =
    Complex.I * finiteC3LegL2Extension M x n
  rw [finiteC3LegL2Extension_apply]
  by_cases hn : n < M <;> simp [hn]

/-- The existing finite camera embedding of a quarter-turned leg is the
global synthesis of the quarter-turned zero extension. -/
theorem finiteC3LegCameraIsometry_I_smul
    (M : ℕ)
    (x : NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace M) :
    finiteC3LegCameraIsometry M (Complex.I • x) =
      completedC3GlobalLegCameraIsometry
        (Complex.I • finiteC3LegL2Extension M x) := by
  rw [← completedC3GlobalLegCameraIsometry_finiteExtension,
    finiteC3LegL2Extension_I_smul]

def completedC3LegCameraState (x : CarryVerticalL2) : CameraHilbert :=
  completedC3GlobalLegCameraIsometry x

/-- The second leg of the genuine C3 port, extended by zero, is exactly the
already-constructed ordinary Hilbert prefix. -/
theorem finiteC3GenuineSecondLegL2Extension_eq_prefix
    (N : ℕ) (s : ℂ) :
    finiteC3LegL2Extension N
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair N s).2 =
      canonicalCompletedC3DirichletGradientPrefixState s N := by
  rw [finiteC3LegL2Extension, Finset.sum_fin_eq_sum_range,
    canonicalCompletedC3DirichletGradientPrefixState_eq_sum_single]
  apply Finset.sum_congr rfl
  intro n hn
  have hnlt : n < N := Finset.mem_range.mp hn
  simp [hnlt,
    NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair_snd_apply]

/-- The real radial coefficient retained by the first genuine C3 leg. -/
def completedC3RadialRealCoefficient (s : ℂ) : ℝ :=
  (3 : ℝ) ^ (-criticalDisplacement s.re)

/-- The first genuine C3 leg is the same ordinary prefix with its real radial
coefficient; no phase or quadrature is discarded. -/
theorem finiteC3GenuineFirstLegL2Extension_eq_radial_prefix
    (N : ℕ) (s : ℂ) :
    finiteC3LegL2Extension N
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair N s).1 =
      (completedC3RadialRealCoefficient s : ℂ) •
        canonicalCompletedC3DirichletGradientPrefixState s N := by
  apply lp.ext
  funext n
  rw [finiteC3LegL2Extension_apply]
  change
    (if h : n < N then
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair N s).1
          ⟨n, h⟩
      else 0) =
      (completedC3RadialRealCoefficient s : ℂ) *
        canonicalCompletedC3DirichletGradientPrefixState s N n
  by_cases hn : n < N
  · rw [dif_pos hn]
    rw [finiteC3GenuineBracketGreenBoundaryPair_fst_eq_radial_mul_completedPrefix]
    rw [canonicalCompletedC3DirichletGradientPrefixState_apply]
    simp [completedC3RadialRealCoefficient]
  · rw [dif_neg hn]
    rw [canonicalCompletedC3DirichletGradientPrefixState_apply]
    simp [hn]

/-- Thus the actual finite second-leg camera vectors are the prefixes of the
single completed camera vector. -/
theorem finiteC3GenuineSecondLegCamera_eq_completedPrefix
    (N : ℕ) (s : ℂ) :
    finiteC3LegCameraIsometry N
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair N s).2 =
      completedC3LegCameraState
        (canonicalCompletedC3DirichletGradientPrefixState s N) := by
  rw [← completedC3GlobalLegCameraIsometry_finiteExtension,
    finiteC3GenuineSecondLegL2Extension_eq_prefix]
  rfl

/-- The actual finite first-leg camera vector is the same real radial multiple
of the global ordinary prefix vector. -/
theorem finiteC3GenuineFirstLegCamera_eq_radial_completedPrefix
    (N : ℕ) (s : ℂ) :
    finiteC3LegCameraIsometry N
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair N s).1 =
      completedC3RadialRealCoefficient s •
        completedC3LegCameraState
          (canonicalCompletedC3DirichletGradientPrefixState s N) := by
  rw [← completedC3GlobalLegCameraIsometry_finiteExtension,
    finiteC3GenuineFirstLegL2Extension_eq_radial_prefix]
  rw [show
      (completedC3RadialRealCoefficient s : ℂ) •
          canonicalCompletedC3DirichletGradientPrefixState s N =
        completedC3RadialRealCoefficient s •
          canonicalCompletedC3DirichletGradientPrefixState s N by rfl,
    map_smul]
  rfl

/-- Ordinary C3 prefixes converge as vectors in the single global camera
Hilbert space. -/
theorem canonicalCompletedC3DirichletGradientPrefixCameraState_tendsto
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun N : ℕ ↦ completedC3LegCameraState
        (canonicalCompletedC3DirichletGradientPrefixState s N))
      atTop
      (nhds (completedC3LegCameraState
        (canonicalCompletedC3DirichletGradientState s hs))) := by
  exact completedC3GlobalLegCameraIsometry.continuous.continuousAt.tendsto.comp
    (canonicalCompletedC3DirichletGradientPrefixState_tendsto hs)

/-- The existing finite second-leg embeddings themselves converge in the
global camera Hilbert space. -/
theorem finiteC3GenuineSecondLegCamera_tendsto
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun N : ℕ ↦ finiteC3LegCameraIsometry N
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair N s).2)
      atTop
      (nhds (completedC3LegCameraState
        (canonicalCompletedC3DirichletGradientState s hs))) := by
  exact (canonicalCompletedC3DirichletGradientPrefixCameraState_tendsto hs).congr'
    (Eventually.of_forall fun N ↦
      (finiteC3GenuineSecondLegCamera_eq_completedPrefix N s).symm)

/-- The actual first-leg camera vectors converge to the radial multiple of the
same completed camera state. -/
theorem finiteC3GenuineFirstLegCamera_tendsto
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun N : ℕ ↦ finiteC3LegCameraIsometry N
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair N s).1)
      atTop
      (nhds (completedC3RadialRealCoefficient s •
        completedC3LegCameraState
          (canonicalCompletedC3DirichletGradientState s hs))) := by
  exact
    ((canonicalCompletedC3DirichletGradientPrefixCameraState_tendsto hs).const_smul
      (completedC3RadialRealCoefficient s)).congr'
      (Eventually.of_forall fun N ↦
        (finiteC3GenuineFirstLegCamera_eq_radial_completedPrefix N s).symm)

/-! ## Vector limit of the symplectic and Naimark states -/

/-- The completed symplectic camera state.  Its two legs remain explicit and
are assembled only after their separate vector limits have been proved. -/
def completedC3SymplecticCameraState
    (s : ℂ) (hs : 0 < s.re) : RealifiedCameraComplexification :=
  WithLp.toLp 2
    (-(completedC3RadialRealCoefficient s •
        completedC3LegCameraState
          (canonicalCompletedC3DirichletGradientState s hs)),
      completedC3LegCameraState
        (canonicalCompletedC3DirichletGradientState s hs))

/-- The genuine finite C3 symplectic packings converge as vectors in one fixed
global camera Hilbert space. -/
theorem finiteC3GenuineSymplecticCameraPacking_tendsto
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun N : ℕ ↦ finiteC3SymplecticCameraPacking N
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair N s))
      atTop
      (nhds (completedC3SymplecticCameraState s hs)) := by
  have hfirst := (finiteC3GenuineFirstLegCamera_tendsto hs).neg
  have hsecond := finiteC3GenuineSecondLegCamera_tendsto hs
  have hpair := hfirst.prodMk_nhds hsecond
  have hlp :=
    (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp hpair
  unfold completedC3SymplecticCameraState
  convert hlp using 1
  funext N
  rfl

/-- Naimark promotion of the completed symplectic camera state. -/
def completedC3SymplecticNaimarkState
    (s : ℂ) (hs : 0 < s.re) : RealifiedNaimarkComplexification :=
  realifiedNaimarkPort (completedC3SymplecticCameraState s hs)

/-- Continuity of the already-constructed Naimark port promotes the camera
vector limit without adding a scalar or spectral hypothesis. -/
theorem finiteC3GenuineSymplecticNaimarkRealization_tendsto
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun N : ℕ ↦ finiteC3SymplecticNaimarkRealization N
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair N s))
      atTop
      (nhds (completedC3SymplecticNaimarkState s hs)) := by
  exact realifiedNaimarkPort.continuous.continuousAt.tendsto.comp
    (finiteC3GenuineSymplecticCameraPacking_tendsto hs)

/-- The same vector convergence on the canonical C3 cutoff subsequence
`N = 3 M`. -/
theorem canonicalC3AllCutoffGenuineSymplecticNaimarkRealization_tendsto
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun M : ℕ ↦ finiteC3SymplecticNaimarkRealization (3 * M)
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
          (3 * M) s))
      atTop
      (nhds (completedC3SymplecticNaimarkState s hs)) := by
  exact (finiteC3GenuineSymplecticNaimarkRealization_tendsto hs).comp
    tendsto_three_mul_atTop

/-! ## The retained quarter-turn channel -/

/-- Completed symplectic state after rotating both complex C3 legs before
realification. -/
def completedC3QuarterTurnSymplecticCameraState
    (s : ℂ) (hs : 0 < s.re) : RealifiedCameraComplexification :=
  WithLp.toLp 2
    (-completedC3GlobalLegCameraIsometry
        (Complex.I •
          ((completedC3RadialRealCoefficient s : ℂ) •
            canonicalCompletedC3DirichletGradientState s hs)),
      completedC3GlobalLegCameraIsometry
        (Complex.I • canonicalCompletedC3DirichletGradientState s hs))

/-- The finite symplectic packing of the quarter-turned genuine port converges
in the same global camera space. -/
theorem finiteC3GenuineQuarterTurnSymplecticCameraPacking_tendsto
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun N : ℕ ↦ finiteC3SymplecticCameraPacking N
        (Complex.I •
          NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair N s))
      atTop
      (nhds (completedC3QuarterTurnSymplecticCameraState s hs)) := by
  have hprefix := canonicalCompletedC3DirichletGradientPrefixState_tendsto hs
  have hfirstSource :=
    (hprefix.const_smul (completedC3RadialRealCoefficient s : ℂ)).const_smul
      Complex.I
  have hsecondSource := hprefix.const_smul Complex.I
  have hfirst :=
    completedC3GlobalLegCameraIsometry.continuous.continuousAt.tendsto.comp
      hfirstSource
  have hsecond :=
    completedC3GlobalLegCameraIsometry.continuous.continuousAt.tendsto.comp
      hsecondSource
  have hpair := hfirst.neg.prodMk_nhds hsecond
  have hlp :=
    (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp hpair
  have hfinite (N : ℕ) :
      finiteC3SymplecticCameraPacking N
          (Complex.I •
            NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair N s) =
        WithLp.toLp 2
          (-completedC3GlobalLegCameraIsometry
              (Complex.I •
                ((completedC3RadialRealCoefficient s : ℂ) •
                  canonicalCompletedC3DirichletGradientPrefixState s N)),
            completedC3GlobalLegCameraIsometry
              (Complex.I •
                canonicalCompletedC3DirichletGradientPrefixState s N)) := by
    rw [finiteC3SymplecticCameraPacking_apply]
    apply congrArg (WithLp.toLp 2)
    apply Prod.ext
    · change
        -finiteC3LegCameraIsometry N
            (Complex.I •
              (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
                N s).1) = _
      rw [finiteC3LegCameraIsometry_I_smul,
        finiteC3GenuineFirstLegL2Extension_eq_radial_prefix]
    · change
        finiteC3LegCameraIsometry N
            (Complex.I •
              (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
                N s).2) = _
      rw [finiteC3LegCameraIsometry_I_smul,
        finiteC3GenuineSecondLegL2Extension_eq_prefix]
  unfold completedC3QuarterTurnSymplecticCameraState
  exact hlp.congr' (Eventually.of_forall fun N ↦ (hfinite N).symm)

/-- Naimark promotion of the retained quarter-turn channel. -/
def completedC3QuarterTurnSymplecticNaimarkState
    (s : ℂ) (hs : 0 < s.re) : RealifiedNaimarkComplexification :=
  realifiedNaimarkPort (completedC3QuarterTurnSymplecticCameraState s hs)

/-- The quarter-turned finite Naimark vectors converge by continuity in the
same ambient Naimark space as the direct vectors. -/
theorem finiteC3GenuineQuarterTurnSymplecticNaimarkRealization_tendsto
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun N : ℕ ↦ finiteC3SymplecticNaimarkRealization N
        (Complex.I •
          NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair N s))
      atTop
      (nhds (completedC3QuarterTurnSymplecticNaimarkState s hs)) := by
  exact realifiedNaimarkPort.continuous.continuousAt.tendsto.comp
    (finiteC3GenuineQuarterTurnSymplecticCameraPacking_tendsto hs)

/-- Canonical `3 M` specialization of the quarter-turn vector limit. -/
theorem canonicalC3AllCutoffGenuineQuarterTurnSymplecticNaimarkRealization_tendsto
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun M : ℕ ↦ finiteC3SymplecticNaimarkRealization (3 * M)
        (Complex.I •
          NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) s))
      atTop
      (nhds (completedC3QuarterTurnSymplecticNaimarkState s hs)) := by
  exact
    (finiteC3GenuineQuarterTurnSymplecticNaimarkRealization_tendsto hs).comp
      tendsto_three_mul_atTop

/-! ## Completed two-quadrature Green readout -/

/-- Direct and quarter-turned Green readings after vector completion.  Both
coordinates live in the same global Naimark space and are retained until the
complex readout is formed. -/
def completedC3MixedSymplecticNaimarkQuadratures
    (z w : ℂ) (hw : 0 < w.re)
    (hzReflected : 0 < (reflectedParameter z).re) :
    FiniteC3SymplecticGreenQuadratures where
  direct := NativeCarryC3Crosswalk.realifiedGreenSkew
    (completedC3SymplecticNaimarkState w hw)
    (completedC3SymplecticNaimarkState
      (reflectedParameter z) hzReflected)
  quarterTurn := NativeCarryC3Crosswalk.realifiedGreenSkew
    (completedC3SymplecticNaimarkState w hw)
    (completedC3QuarterTurnSymplecticNaimarkState
      (reflectedParameter z) hzReflected)

/-- Complex Green readout formed only after both completed real quadratures
have been retained. -/
def completedC3MixedSymplecticNaimarkGreenReadout
    (z w : ℂ) (hw : 0 < w.re)
    (hzReflected : 0 < (reflectedParameter z).re) : ℂ :=
  (completedC3MixedSymplecticNaimarkQuadratures
    z w hw hzReflected).complexReadout

/-- The finite direct Naimark quadrature converges to the direct reading of
the two completed vectors. -/
theorem canonicalC3FiniteMixedSymplecticNaimarkQuadrature_direct_tendsto
    {z w : ℂ} (hw : 0 < w.re)
    (hzReflected : 0 < (reflectedParameter z).re) :
    Tendsto
      (fun M : ℕ ↦
        (canonicalC3FiniteMixedSymplecticNaimarkQuadratures M z w).direct)
      atTop
      (nhds
        (completedC3MixedSymplecticNaimarkQuadratures
          z w hw hzReflected).direct) := by
  have hwLimit :=
    canonicalC3AllCutoffGenuineSymplecticNaimarkRealization_tendsto hw
  have hzLimit :=
    canonicalC3AllCutoffGenuineSymplecticNaimarkRealization_tendsto
      hzReflected
  unfold canonicalC3FiniteMixedSymplecticNaimarkQuadratures
    finiteC3SymplecticNaimarkGreenQuadratures
    completedC3MixedSymplecticNaimarkQuadratures
    NativeCarryC3Crosswalk.realifiedGreenSkew
  exact (Filter.Tendsto.inner
      ((WithLp.continuous_fst 2 NaimarkSpace NaimarkSpace).continuousAt.tendsto.comp
        hwLimit)
      ((WithLp.continuous_snd 2 NaimarkSpace NaimarkSpace).continuousAt.tendsto.comp
        hzLimit)).sub
    (Filter.Tendsto.inner
      ((WithLp.continuous_snd 2 NaimarkSpace NaimarkSpace).continuousAt.tendsto.comp
        hwLimit)
      ((WithLp.continuous_fst 2 NaimarkSpace NaimarkSpace).continuousAt.tendsto.comp
        hzLimit))

/-- The finite quarter-turn Naimark quadrature converges independently to
the retained quarter-turn reading of the completed vectors. -/
theorem canonicalC3FiniteMixedSymplecticNaimarkQuadrature_quarterTurn_tendsto
    {z w : ℂ} (hw : 0 < w.re)
    (hzReflected : 0 < (reflectedParameter z).re) :
    Tendsto
      (fun M : ℕ ↦
        (canonicalC3FiniteMixedSymplecticNaimarkQuadratures M z w).quarterTurn)
      atTop
      (nhds
        (completedC3MixedSymplecticNaimarkQuadratures
          z w hw hzReflected).quarterTurn) := by
  have hwLimit :=
    canonicalC3AllCutoffGenuineSymplecticNaimarkRealization_tendsto hw
  have hzLimit :=
    canonicalC3AllCutoffGenuineQuarterTurnSymplecticNaimarkRealization_tendsto
      hzReflected
  unfold canonicalC3FiniteMixedSymplecticNaimarkQuadratures
    finiteC3SymplecticNaimarkGreenQuadratures
    completedC3MixedSymplecticNaimarkQuadratures
    NativeCarryC3Crosswalk.realifiedGreenSkew
  exact (Filter.Tendsto.inner
      ((WithLp.continuous_fst 2 NaimarkSpace NaimarkSpace).continuousAt.tendsto.comp
        hwLimit)
      ((WithLp.continuous_snd 2 NaimarkSpace NaimarkSpace).continuousAt.tendsto.comp
        hzLimit)).sub
    (Filter.Tendsto.inner
      ((WithLp.continuous_snd 2 NaimarkSpace NaimarkSpace).continuousAt.tendsto.comp
        hwLimit)
      ((WithLp.continuous_fst 2 NaimarkSpace NaimarkSpace).continuousAt.tendsto.comp
        hzLimit))

/-- The lossless complex reconstruction commutes with the all-cutoff vector
limit. -/
theorem canonicalC3FiniteMixedSymplecticNaimarkGreenReadout_tendsto_vector
    {z w : ℂ} (hw : 0 < w.re)
    (hzReflected : 0 < (reflectedParameter z).re) :
    Tendsto
      (fun M : ℕ ↦ canonicalC3FiniteMixedSymplecticNaimarkGreenReadout
        M z w)
      atTop
      (nhds
        (completedC3MixedSymplecticNaimarkGreenReadout
          z w hw hzReflected)) := by
  have hdirect :=
    canonicalC3FiniteMixedSymplecticNaimarkQuadrature_direct_tendsto
      hw hzReflected
  have hquarter :=
    canonicalC3FiniteMixedSymplecticNaimarkQuadrature_quarterTurn_tendsto
      hw hzReflected
  simpa [canonicalC3FiniteMixedSymplecticNaimarkGreenReadout,
    completedC3MixedSymplecticNaimarkGreenReadout,
    FiniteC3SymplecticGreenQuadratures.complexReadout] using
      hdirect.ofReal.sub (tendsto_const_nhds.mul hquarter.ofReal)

/-- The completed radial Green kernel is literally the lossless readout of
the two completed Naimark vectors.  This is a vector identity obtained by
uniqueness of the common finite limit, not by scalar channel cancellation. -/
theorem completedC3MixedSymplecticNaimarkGreenReadout_eq_radialKernel
    {z w : ℂ} (hw : 0 < w.re)
    (hzReflected : 0 < (reflectedParameter z).re) :
    completedC3MixedSymplecticNaimarkGreenReadout z w hw hzReflected =
      canonicalCompletedC3MixedRadialGreenKernel
        z w hw hzReflected := by
  exact tendsto_nhds_unique
    (canonicalC3FiniteMixedSymplecticNaimarkGreenReadout_tendsto_vector
      hw hzReflected)
    (canonicalC3FiniteMixedSymplecticNaimarkGreenReadout_tendsto_completed
      hw hzReflected)

/-! ## Positive product on the same completed carrier -/

/-- The completed vector viewed through the canonical complex Hilbert
structure on the same two real Naimark quadratures.  This is a definitional
change of type presentation; no coordinate map is applied. -/
def completedC3SymplecticNaimarkComplexState
    (z : ℂ) (hz : 0 < z.re) :
    RealHilbertComplexification NaimarkSpace :=
  completedC3SymplecticNaimarkState z hz

/-- Ordinary complex Hilbert product of the completed symplectic Naimark
states.  This uses the same ambient vectors as the preceding Green readout;
only the final bilinear operation changes from symplectic skew to Hilbert
product. -/
def completedC3SymplecticNaimarkGram
    (z w : ℂ) (hz : 0 < z.re) (hw : 0 < w.re) : ℂ :=
  inner ℂ
    (completedC3SymplecticNaimarkComplexState z hz)
    (completedC3SymplecticNaimarkComplexState w hw)

/-- The diagonal of the completed Naimark Gram is exactly a squared norm. -/
theorem completedC3SymplecticNaimarkGram_self
    (z : ℂ) (hz : 0 < z.re) :
    completedC3SymplecticNaimarkGram z z hz hz =
      ((‖completedC3SymplecticNaimarkComplexState z hz‖ : ℝ) : ℂ) ^ 2 := by
  simp [completedC3SymplecticNaimarkGram, inner_self_eq_norm_sq_to_K]

/-- In particular, the real diagonal of the uncollapsed completed state is
nonnegative. -/
theorem completedC3SymplecticNaimarkGram_self_re_nonneg
    (z : ℂ) (hz : 0 < z.re) :
    0 ≤ (completedC3SymplecticNaimarkGram z z hz hz).re := by
  rw [completedC3SymplecticNaimarkGram_self]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  positivity

/-- Every finite section of the completed all-cutoff Naimark product is
positive semidefinite.  No Green channel is set to zero in this statement;
the vectors are exactly those used by the completed two-quadrature readout. -/
theorem completedC3SymplecticNaimarkGram_posSemidef
    {ι : Type*} [Finite ι]
    (point : ι → ℂ) (hpos : ∀ i, 0 < (point i).re) :
    (Matrix.of fun i j ↦
      completedC3SymplecticNaimarkGram
        (point i) (point j) (hpos i) (hpos j)).PosSemidef := by
  change (Matrix.gram ℂ (fun i ↦
    completedC3SymplecticNaimarkComplexState
      (point i) (hpos i))).PosSemidef
  exact Matrix.posSemidef_gram ℂ _

end

end CarrySelfAdjointOperator
