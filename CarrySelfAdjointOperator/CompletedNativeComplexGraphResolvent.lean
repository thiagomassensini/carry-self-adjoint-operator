import CarrySelfAdjointOperator.CompletedNativeJacobiWeylContinuation
import CarrySelfAdjointOperator.LinearPMapMeromorphicResolvent
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Tactic

/-!
# Complex graph resolvent of the completed native Jacobi operator

The completed Green construction already gives a real cyclic orbit
`v_n = A^n v_0` for the positive maximal-adjoint square `A = B* B`, together
with a geometric norm bound.  This file complexifies that orbit before taking
the power-series sum.  The resulting vector-valued germ is analytic, lies in
the graph of the complexified operator, and satisfies the exact resolvent
equation.

This construction uses the Green/Jacobi carrier.  It does not reuse the
radially normalized C3 state, whose complex differentiability obstruction is
recorded separately in `BR2RadialNormalizedComplexJetNoGo`.
-/

open scoped BigOperators InnerProductSpace LinearPMap RealInnerProductSpace
open Filter Set Topology

namespace CarrySelfAdjointOperator

noncomputable section

namespace ComplexifiedOrbitResolvent

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E]

/-- Embed one real vector as the real quadrature of its Hilbert
complexification. -/
def ofReal (x : E) : RealHilbertComplexification E :=
  RealHilbertComplexification.mk x 0

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
@[simp] theorem re_ofReal (x : E) :
    RealHilbertComplexification.re (ofReal x) = x :=
  rfl

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
@[simp] theorem im_ofReal (x : E) :
    RealHilbertComplexification.im (ofReal x) = 0 :=
  rfl

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
@[simp] theorem norm_ofReal (x : E) : ‖ofReal x‖ = ‖x‖ := by
  have hsq : ‖ofReal x‖ ^ 2 = ‖x‖ ^ 2 := by
    calc
      ‖ofReal x‖ ^ 2 =
          ‖RealHilbertComplexification.re (ofReal x)‖ ^ 2 +
            ‖RealHilbertComplexification.im (ofReal x)‖ ^ 2 :=
        WithLp.prod_norm_sq_eq_of_L2 (ofReal x)
      _ = ‖x‖ ^ 2 := by
        rw [re_ofReal, im_ofReal, norm_zero]
        norm_num
  nlinarith [norm_nonneg (ofReal x), norm_nonneg x]

/-- Formal complex power series of a real Hilbert-space orbit. -/
def series (v : ℕ → E) :
    FormalMultilinearSeries ℂ ℂ (RealHilbertComplexification E) :=
  fun n =>
    (ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ).smulRight
      (ofReal (v n))

/-- Vector-valued sum of the complexified orbit.  It is total; the theorems
below use the positive convergence radius forced by the geometric bound. -/
def state (v : ℕ → E) (u : ℂ) : RealHilbertComplexification E :=
  (series v).sum u

omit [CompleteSpace E] in
@[simp] theorem series_apply (v : ℕ → E) (n : ℕ) (u : ℂ) :
    series v n (fun _ => u) = u ^ n • ofReal (v n) := by
  simp [series, ContinuousMultilinearMap.mkPiAlgebraFin_apply]

omit [CompleteSpace E] in
/-- A geometric norm bound gives the complexified orbit series a nonzero
radius of convergence. -/
theorem series_radius_pos
    {v : ℕ → E}
    (hbound : ∃ D r : ℝ, 0 < D ∧ 0 < r ∧
      ∀ n : ℕ, ‖v n‖ ≤ D * r ^ n) :
    0 < (series v).radius := by
  obtain ⟨D, r, hD, hr, hbound⟩ := hbound
  let ρ : NNReal := ⟨1 / (2 * r), by positivity⟩
  have hρpos : 0 < ρ := by
    change 0 < 1 / (2 * r)
    positivity
  have hρle : (ρ : ENNReal) ≤ (series v).radius := by
    apply (series v).le_radius_of_bound D
    intro n
    change
      ‖(ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ).smulRight
          (ofReal (v n))‖ * (ρ : ℝ) ^ n ≤ D
    rw [ContinuousMultilinearMap.norm_smulRight,
      ContinuousMultilinearMap.norm_mkPiAlgebraFin, one_mul, norm_ofReal]
    calc
      ‖v n‖ * (ρ : ℝ) ^ n ≤
          (D * r ^ n) * (ρ : ℝ) ^ n := by
        exact mul_le_mul_of_nonneg_right (hbound n) (by positivity)
      _ = D * (1 / 2 : ℝ) ^ n := by
        rw [mul_assoc, ← mul_pow]
        congr 2
        change r * (1 / (2 * r)) = (1 / 2 : ℝ)
        field_simp [ne_of_gt hr]
      _ ≤ D := by
        exact mul_le_of_le_one_right hD.le
          (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by norm_num : (1 / 2 : ℝ) ≤ 1))
  exact lt_of_lt_of_le (by exact_mod_cast hρpos) hρle

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- A geometric orbit bound automatically bounds the shifted orbit on the
same scale. -/
theorem shifted_geometricBound
    {v : ℕ → E}
    (hbound : ∃ D r : ℝ, 0 < D ∧ 0 < r ∧
      ∀ n : ℕ, ‖v n‖ ≤ D * r ^ n) :
    ∃ D r : ℝ, 0 < D ∧ 0 < r ∧
      ∀ n : ℕ, ‖v (n + 1)‖ ≤ D * r ^ n := by
  obtain ⟨D, r, hD, hr, hbound⟩ := hbound
  refine ⟨D * r, r, mul_pos hD hr, hr, fun n => ?_⟩
  calc
    ‖v (n + 1)‖ ≤ D * r ^ (n + 1) := hbound (n + 1)
    _ = (D * r) * r ^ n := by rw [pow_succ]; ring

/-- The orbit sum is an analytic Hilbert-valued germ. -/
theorem state_hasFPowerSeriesAt
    {v : ℕ → E}
    (hbound : ∃ D r : ℝ, 0 < D ∧ 0 < r ∧
      ∀ n : ℕ, ‖v n‖ ≤ D * r ^ n) :
    HasFPowerSeriesAt (state v) (series v) 0 :=
  ((series v).hasFPowerSeriesOnBall (series_radius_pos hbound)).hasFPowerSeriesAt

theorem state_analyticAt
    {v : ℕ → E}
    (hbound : ∃ D r : ℝ, 0 < D ∧ 0 < r ∧
      ∀ n : ℕ, ‖v n‖ ≤ D * r ^ n) :
    AnalyticAt ℂ (state v) 0 :=
  (state_hasFPowerSeriesAt hbound).analyticAt

omit [CompleteSpace E] in
/-- Each orbit coefficient and its successor form a point in the graph of
the complexified operator. -/
theorem ofReal_pair_mem_complexification_graph
    (A : E →ₗ.[ℝ] E) {v : ℕ → E}
    (horbit : ∀ n : ℕ, ∃ x : A.domain,
      (x : E) = v n ∧ A x = v (n + 1))
    (n : ℕ) :
    (ofReal (v n), ofReal (v (n + 1))) ∈ A.complexification.graph := by
  obtain ⟨x, hx, hAx⟩ := horbit n
  rw [LinearPMap.mem_graph_iff]
  let xc : A.complexification.domain :=
    ⟨ofReal (v n), by
      change
        RealHilbertComplexification.re (ofReal (v n)) ∈ A.domain ∧
          RealHilbertComplexification.im (ofReal (v n)) ∈ A.domain
      constructor
      · simpa [hx] using x.property
      · exact A.domain.zero_mem⟩
  refine ⟨xc, rfl, ?_⟩
  apply RealHilbertComplexification.ext
  · have hre : A.complexificationDomainRe xc = x := by
      apply Subtype.ext
      exact hx.symm
    rw [LinearPMap.re_complexification_apply, hre, hAx, re_ofReal]
  · change A ⟨0, A.domain.zero_mem⟩ = 0
    rw [show (⟨0, A.domain.zero_mem⟩ : A.domain) = 0 by rfl]
    exact A.map_zero

omit [CompleteSpace E] in
/-- Complexification preserves closed graphs.  The proof keeps the real and
imaginary graph channels separate and intersects their two closed preimages. -/
theorem complexification_isClosed
    (A : E →ₗ.[ℝ] E) (hA : A.IsClosed) :
    A.complexification.IsClosed := by
  let pairRe :
      (RealHilbertComplexification E × RealHilbertComplexification E) →
        E × E := fun p =>
    (RealHilbertComplexification.re p.1,
      RealHilbertComplexification.re p.2)
  let pairIm :
      (RealHilbertComplexification E × RealHilbertComplexification E) →
        E × E := fun p =>
    (RealHilbertComplexification.im p.1,
      RealHilbertComplexification.im p.2)
  have hpairRe : Continuous pairRe := by
    dsimp only [pairRe, RealHilbertComplexification.re]
    fun_prop
  have hpairIm : Continuous pairIm := by
    dsimp only [pairIm, RealHilbertComplexification.im]
    fun_prop
  have hset : (A.complexification.graph :
      Set (RealHilbertComplexification E × RealHilbertComplexification E)) =
      pairRe ⁻¹' A.graph ∩ pairIm ⁻¹' A.graph := by
    ext p
    constructor
    · intro hp
      rcases (LinearPMap.mem_graph_iff A.complexification).mp hp with
        ⟨x, hx, hAx⟩
      constructor
      · let xr := A.complexificationDomainRe x
        have hpair :
            (RealHilbertComplexification.re p.1,
              RealHilbertComplexification.re p.2) =
            ((xr : E), A xr) := by
          apply Prod.ext
          · exact (congrArg RealHilbertComplexification.re hx).symm
          · exact ((LinearPMap.re_complexification_apply A x).symm.trans
              (congrArg RealHilbertComplexification.re hAx)).symm
        change
          (RealHilbertComplexification.re p.1,
            RealHilbertComplexification.re p.2) ∈ A.graph
        rw [hpair]
        exact A.mem_graph xr
      · let xi := A.complexificationDomainIm x
        have hpair :
            (RealHilbertComplexification.im p.1,
              RealHilbertComplexification.im p.2) =
            ((xi : E), A xi) := by
          apply Prod.ext
          · exact (congrArg RealHilbertComplexification.im hx).symm
          · exact ((LinearPMap.im_complexification_apply A x).symm.trans
              (congrArg RealHilbertComplexification.im hAx)).symm
        change
          (RealHilbertComplexification.im p.1,
            RealHilbertComplexification.im p.2) ∈ A.graph
        rw [hpair]
        exact A.mem_graph xi
    · rintro ⟨hre, him⟩
      change pairRe p ∈ A.graph at hre
      change pairIm p ∈ A.graph at him
      rcases (LinearPMap.mem_graph_iff A).mp hre with ⟨xr, hxr, hAxr⟩
      rcases (LinearPMap.mem_graph_iff A).mp him with ⟨xi, hxi, hAxi⟩
      dsimp only [pairRe] at hxr hAxr
      dsimp only [pairIm] at hxi hAxi
      let x : A.complexification.domain :=
        ⟨p.1, by
          change
            RealHilbertComplexification.re p.1 ∈ A.domain ∧
              RealHilbertComplexification.im p.1 ∈ A.domain
          exact ⟨by rw [← hxr]; exact xr.property,
            by rw [← hxi]; exact xi.property⟩⟩
      apply (LinearPMap.mem_graph_iff A.complexification).2
      refine ⟨x, rfl, ?_⟩
      apply RealHilbertComplexification.ext
      · rw [LinearPMap.re_complexification_apply]
        have hxre : A.complexificationDomainRe x = xr := by
          apply Subtype.ext
          exact hxr.symm
        rw [hxre]
        exact hAxr
      · rw [LinearPMap.im_complexification_apply]
        have hxim : A.complexificationDomainIm x = xi := by
          apply Subtype.ext
          exact hxi.symm
        rw [hxim]
        exact hAxi
  change _root_.IsClosed
    (A.complexification.graph :
      Set (RealHilbertComplexification E × RealHilbertComplexification E))
  rw [hset]
  exact hA.preimage hpairRe |>.inter (hA.preimage hpairIm)

/-- The two analytic orbit sums form a graph-valued germ of the complexified
closed operator. -/
theorem eventually_pair_mem_graph
    (A : E →ₗ.[ℝ] E)
    (hA : A.complexification.IsClosed)
    {v : ℕ → E}
    (hbound : ∃ D r : ℝ, 0 < D ∧ 0 < r ∧
      ∀ n : ℕ, ‖v n‖ ≤ D * r ^ n)
    (horbit : ∀ n : ℕ, ∃ x : A.domain,
      (x : E) = v n ∧ A x = v (n + 1)) :
    ∀ᶠ u : ℂ in nhds 0,
      (state v u, state (fun n => v (n + 1)) u) ∈
        A.complexification.graph := by
  have hx := (state_hasFPowerSeriesAt hbound).eventually_hasSum
  have hy := (state_hasFPowerSeriesAt
    (shifted_geometricBound hbound)).eventually_hasSum
  filter_upwards [hx, hy] with u hxu hyu
  apply hA.mem_of_tendsto
    (by simpa only [zero_add] using
      hxu.tendsto_sum_nat.prodMk_nhds hyu.tendsto_sum_nat)
  filter_upwards [] with N
  rw [show
    ((∑ i ∈ Finset.range N, (series v i) fun _ => u),
      ∑ i ∈ Finset.range N,
        (series (fun n => v (n + 1)) i) fun _ => u) =
      ∑ i ∈ Finset.range N,
        ((series v i) (fun _ => u),
          (series (fun n => v (n + 1)) i) (fun _ => u)) by
    apply Prod.ext
    · rw [Prod.fst_sum]
    · rw [Prod.snd_sum]]
  apply A.complexification.graph.sum_mem
  intro n hn
  simpa [series, ContinuousMultilinearMap.mkPiAlgebraFin_apply] using
    A.complexification.graph.smul_mem (u ^ n)
      (ofReal_pair_mem_complexification_graph A horbit n)

/-- The orbit germ satisfies the exact complex resolvent identity.  The
terminal vector is not discarded: it vanishes because it is a term of the
convergent Hilbert-valued power series. -/
theorem eventually_resolventEquation
    {v : ℕ → E}
    (hbound : ∃ D r : ℝ, 0 < D ∧ 0 < r ∧
      ∀ n : ℕ, ‖v n‖ ≤ D * r ^ n) :
    ∀ᶠ u : ℂ in nhds 0,
      state v u - u • state (fun n => v (n + 1)) u = ofReal (v 0) := by
  have hx := (state_hasFPowerSeriesAt hbound).eventually_hasSum
  have hy := (state_hasFPowerSeriesAt
    (shifted_geometricBound hbound)).eventually_hasSum
  filter_upwards [hx, hy] with u hxu hyu
  have hxu' : HasSum (fun n => u ^ n • ofReal (v n)) (state v u) := by
    simpa only [zero_add, series_apply] using hxu
  have hyu' : HasSum (fun n => u ^ n • ofReal (v (n + 1)))
      (state (fun n => v (n + 1)) u) := by
    simpa only [zero_add, series_apply] using hyu
  have htail : HasSum (fun n => u ^ (n + 1) • ofReal (v (n + 1)))
      (state v u - ofReal (v 0)) := by
    simpa only [Finset.sum_range_one, series_apply, pow_zero, one_smul,
      Nat.add_comm] using (hasSum_nat_add_iff' 1).mpr hxu'
  have hscaled : HasSum (fun n => u ^ (n + 1) • ofReal (v (n + 1)))
      (u • state (fun n => v (n + 1)) u) := by
    simpa only [smul_smul, pow_succ', mul_comm] using
      hyu'.const_smul u
  have heq : u • state (fun n => v (n + 1)) u =
      state v u - ofReal (v 0) :=
    hscaled.unique htail
  rw [heq]
  abel

/-- Graph-valued analytic germ of the complexified orbit resolvent. -/
def graphState (v : ℕ → E) (u : ℂ) :
    RealHilbertComplexification E × RealHilbertComplexification E :=
  (state v u, state (fun n => v (n + 1)) u)

theorem graphState_analyticAt
    {v : ℕ → E}
    (hbound : ∃ D r : ℝ, 0 < D ∧ 0 < r ∧
      ∀ n : ℕ, ‖v n‖ ≤ D * r ^ n) :
    AnalyticAt ℂ (graphState v) 0 := by
  exact (state_analyticAt hbound).prod
    (state_analyticAt (shifted_geometricBound hbound))

theorem graphState_meromorphicAt
    {v : ℕ → E}
    (hbound : ∃ D r : ℝ, 0 < D ∧ 0 < r ∧
      ∀ n : ℕ, ‖v n‖ ≤ D * r ^ n) :
    MeromorphicAt (graphState v) 0 :=
  (graphState_analyticAt hbound).meromorphicAt

omit [CompleteSpace E] in
/-- Continuous cyclic readout against a real head vector, after
complexification. -/
def headReadout (head : E) : RealHilbertComplexification E →L[ℂ] ℂ :=
  innerSL ℂ (ofReal head)

omit [CompleteSpace E] in
@[simp] theorem headReadout_ofReal (head x : E) :
    headReadout head (ofReal x) = (inner ℝ head x : ℂ) := by
  simp [headReadout, innerSL_apply_apply,
    RealHilbertComplexification.inner_apply,
    RealHilbertComplexification.complexInner]

/-- Coefficientwise identification globalizes to equality of the two
analytic germs. -/
theorem eventually_headReadout_state_eq
    {v : ℕ → E} {coeff : ℕ → ℂ} {f : ℂ → ℂ}
    (head : E)
    (hbound : ∃ D r : ℝ, 0 < D ∧ 0 < r ∧
      ∀ n : ℕ, ‖v n‖ ≤ D * r ^ n)
    (hcoeff : ∀ n : ℕ, (inner ℝ head (v n) : ℂ) = coeff n)
    (hf : ∀ᶠ u : ℂ in nhds 0,
      HasSum (fun n : ℕ => u ^ n * coeff n) (f u)) :
    ∀ᶠ u : ℂ in nhds 0, headReadout head (state v u) = f u := by
  have hv := (state_hasFPowerSeriesAt hbound).eventually_hasSum
  filter_upwards [hv, hf] with u hvu hfu
  have hvu' : HasSum (fun n => series v n (fun _ => u)) (state v u) := by
    simpa only [zero_add] using hvu
  have hmapped := hvu'.mapL (headReadout head)
  apply hmapped.unique
  convert hfu using 1
  funext n
  change headReadout head (series v n (fun _ => u)) = u ^ n * coeff n
  rw [series_apply, map_smul, headReadout_ofReal, hcoeff]
  exact smul_eq_mul _ _

/-- Local graph-resolvent certificate.  The vector, its operator image, and
the scalar readout remain part of one typed object. -/
structure GermCertificate
    (A : E →ₗ.[ℝ] E)
    (source : RealHilbertComplexification E)
    (scalar : ℂ → ℂ) where
  graphResolvent : ℂ →
    RealHilbertComplexification E × RealHilbertComplexification E
  readout :
    (RealHilbertComplexification E × RealHilbertComplexification E) →L[ℂ] ℂ
  analyticAt : AnalyticAt ℂ graphResolvent 0
  eventually_mem_graph : ∀ᶠ u : ℂ in nhds 0,
    graphResolvent u ∈ A.complexification.graph
  eventually_resolventEquation : ∀ᶠ u : ℂ in nhds 0,
    (graphResolvent u).1 - u • (graphResolvent u).2 = source
  eventually_readout_eq : ∀ᶠ u : ℂ in nhds 0,
    readout (graphResolvent u) = scalar u

/-- Construct the complete local certificate from one geometrically bounded
cyclic orbit of a closed real operator. -/
def germCertificate_of_orbit
    (A : E →ₗ.[ℝ] E) (hA : A.IsClosed)
    {v : ℕ → E} {coeff : ℕ → ℂ} {f : ℂ → ℂ}
    (hbound : ∃ D r : ℝ, 0 < D ∧ 0 < r ∧
      ∀ n : ℕ, ‖v n‖ ≤ D * r ^ n)
    (horbit : ∀ n : ℕ, ∃ x : A.domain,
      (x : E) = v n ∧ A x = v (n + 1))
    (hcoeff : ∀ n : ℕ, (inner ℝ (v 0) (v n) : ℂ) = coeff n)
    (hf : ∀ᶠ u : ℂ in nhds 0,
      HasSum (fun n : ℕ => u ^ n * coeff n) (f u)) :
    GermCertificate A (ofReal (v 0)) f where
  graphResolvent := graphState v
  readout := (headReadout (v 0)).comp
    (ContinuousLinearMap.fst ℂ
      (RealHilbertComplexification E) (RealHilbertComplexification E))
  analyticAt := graphState_analyticAt hbound
  eventually_mem_graph :=
    eventually_pair_mem_graph A (complexification_isClosed A hA) hbound horbit
  eventually_resolventEquation := eventually_resolventEquation hbound
  eventually_readout_eq := by
    simpa [graphState] using
      (eventually_headReadout_state_eq
        (v := v) (coeff := coeff) (f := f) (v 0) hbound hcoeff hf)

/-- Height-coordinate form of a local graph resolvent.  The positive Jacobi
parameter is retained explicitly as `z^2`; it is not replaced by `z` or by a
scalar projection. -/
structure HeightGermCertificate
    (A : E →ₗ.[ℝ] E)
    (source : RealHilbertComplexification E)
    (scalar : ℂ → ℂ) where
  graphResolvent : ℂ →
    RealHilbertComplexification E × RealHilbertComplexification E
  readout :
    (RealHilbertComplexification E × RealHilbertComplexification E) →L[ℂ] ℂ
  analyticAt : AnalyticAt ℂ graphResolvent 0
  eventually_mem_graph : ∀ᶠ z : ℂ in nhds 0,
    graphResolvent z ∈ A.complexification.graph
  eventually_resolventEquation : ∀ᶠ z : ℂ in nhds 0,
    (graphResolvent z).1 - z ^ 2 • (graphResolvent z).2 = source
  eventually_readout_eq : ∀ᶠ z : ℂ in nhds 0,
    readout (graphResolvent z) = scalar z

private theorem square_tendsto_zero :
    Tendsto (fun z : ℂ => z ^ 2) (nhds 0) (nhds 0) := by
  have h : ContinuousAt (fun z : ℂ => z ^ 2) 0 := by fun_prop
  simpa using h.tendsto

/-- Reparameterize the complex Jacobi germ by the exact height coordinate
`u = z^2`. -/
def GermCertificate.squareReparameterization
    {A : E →ₗ.[ℝ] E}
    {source : RealHilbertComplexification E} {scalar : ℂ → ℂ}
    (germ : GermCertificate A source scalar) :
    HeightGermCertificate A source (fun z => scalar (z ^ 2)) where
  graphResolvent := fun z => germ.graphResolvent (z ^ 2)
  readout := germ.readout
  analyticAt := by
    have hsquare : AnalyticAt ℂ (fun z : ℂ => z ^ 2) 0 := by fun_prop
    have houter : AnalyticAt ℂ germ.graphResolvent
        ((fun z : ℂ => z ^ 2) 0) := by
      simpa using germ.analyticAt
    have hcomp := AnalyticAt.comp (f := fun z : ℂ => z ^ 2) (x := 0)
      houter hsquare
    exact hcomp.congr (Filter.Eventually.of_forall fun _ => rfl)
  eventually_mem_graph :=
    square_tendsto_zero.eventually germ.eventually_mem_graph
  eventually_resolventEquation :=
    square_tendsto_zero.eventually germ.eventually_resolventEquation
  eventually_readout_eq :=
    square_tendsto_zero.eventually germ.eventually_readout_eq

/-- Replace the scalar name of a height germ by an eventually equal canonical
continuation, leaving the vector-valued graph state unchanged. -/
def HeightGermCertificate.congrScalar
    {A : E →ₗ.[ℝ] E}
    {source : RealHilbertComplexification E} {scalar scalar' : ℂ → ℂ}
    (germ : HeightGermCertificate A source scalar)
    (hscalar : scalar =ᶠ[nhds 0] scalar') :
    HeightGermCertificate A source scalar' where
  graphResolvent := germ.graphResolvent
  readout := germ.readout
  analyticAt := germ.analyticAt
  eventually_mem_graph := germ.eventually_mem_graph
  eventually_resolventEquation := germ.eventually_resolventEquation
  eventually_readout_eq := by
    filter_upwards [germ.eventually_readout_eq, hscalar] with z hz hscalarz
    exact hz.trans hscalarz

end ComplexifiedOrbitResolvent

namespace CompletedNativeGreenWeylReducedHeightCertificate

open ComplexifiedOrbitResolvent

variable {Hxi : Type*}
variable [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
variable {xiState : ℂ → Hxi} {moments : ℕ → ℝ}

@[reducible] local instance completedNativeAmbientRealInnerProductSpace :
    InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
  InnerProductSpace.rclikeToReal ℂ _

/-- The concrete completed Green jet used by the Jacobi operator. -/
abbrev completedJacobiGreenJet (xiState : ℂ → Hxi) :=
  completedGreenJet (canonicalCompletedNativeGreenParityJet xiState)

/-- Closed even carrier of the concrete completed Green jet. -/
abbrev CompletedJacobiEvenCarrier (xiState : ℂ → Hxi) :=
  greenJetEvenHilbertSubspace (completedJacobiGreenJet xiState)

local instance completedJacobiEvenCarrierCompleteSpace
    (xiState : ℂ → Hxi) : CompleteSpace (CompletedJacobiEvenCarrier xiState) :=
  (greenJetEvenHilbertSubspace_isClosed
    (completedJacobiGreenJet xiState)).completeSpace_coe

/-- Cyclic completed Green orbit on which the positive Jacobi operator acts by
one exact forward shift. -/
def completedJacobiOrbit (xiState : ℂ → Hxi) (n : ℕ) :
    CompletedJacobiEvenCarrier xiState :=
  greenJetEvenSectorJet (completedJacobiGreenJet xiState) n

/-- Concrete positive closed Jacobi operator `B*B` on the completed even
Green carrier. -/
def completedJacobiEnergyOperator
    (certificate :
      CompletedNativeGreenWeylReducedHeightCertificate xiState moments) :
    CompletedJacobiEvenCarrier xiState →ₗ.[ℝ]
      CompletedJacobiEvenCarrier xiState :=
  closedGreenJetEnergyAdjointSquare
    (completedGreenJet_gramRepresentation certificate.realMomentKernel)
    (completedGreenJet_even_linearIndependent certificate.evenIndependent)
    (completedGreenJet_odd_linearIndependent certificate.oddIndependent)

theorem completedJacobiEnergyOperator_isClosed
    (certificate :
      CompletedNativeGreenWeylReducedHeightCertificate xiState moments) :
    (completedJacobiEnergyOperator certificate).IsClosed :=
  closedGreenJetEnergyAdjointSquare_isClosed
    (completedGreenJet_gramRepresentation certificate.realMomentKernel)
    (completedGreenJet_even_linearIndependent certificate.evenIndependent)
    (completedGreenJet_odd_linearIndependent certificate.oddIndependent)

theorem completedJacobiOrbit_geometricBound
    (certificate :
      CompletedNativeGreenWeylReducedHeightCertificate xiState moments) :
    ∃ D r : ℝ, 0 < D ∧ 0 < r ∧
      ∀ n : ℕ, ‖completedJacobiOrbit xiState n‖ ≤ D * r ^ n := by
  simpa only [completedJacobiOrbit, completedJacobiGreenJet] using
    certificate.completedGreenEvenJet_norm_geometricBound

theorem completedJacobiOrbit_isOperatorOrbit
    (certificate :
      CompletedNativeGreenWeylReducedHeightCertificate xiState moments) :
    ∀ n : ℕ, ∃ x : (completedJacobiEnergyOperator certificate).domain,
      (x : CompletedJacobiEvenCarrier xiState) =
          completedJacobiOrbit xiState n ∧
        completedJacobiEnergyOperator certificate x =
          completedJacobiOrbit xiState (n + 1) := by
  intro n
  let x : (completedJacobiEnergyOperator certificate).domain :=
    greenJetEvenCoreInClosedAdjointSquareDomain
      (completedGreenJet_gramRepresentation certificate.realMomentKernel)
      (completedGreenJet_even_linearIndependent certificate.evenIndependent)
      (completedGreenJet_odd_linearIndependent certificate.oddIndependent)
      (greenJetEvenCoreJet (completedJacobiGreenJet xiState) n)
  refine ⟨x, rfl, ?_⟩
  exact closedGreenJetEnergyAdjointSquare_apply_cyclicJet
    (completedGreenJet_gramRepresentation certificate.realMomentKernel)
    (completedGreenJet_even_linearIndependent certificate.evenIndependent)
    (completedGreenJet_odd_linearIndependent certificate.oddIndependent) n

theorem completedJacobiOrbit_head_inner_eq_canonicalMoment
    (certificate :
      CompletedNativeGreenWeylReducedHeightCertificate xiState moments)
    (n : ℕ) :
    (inner ℝ (completedJacobiOrbit xiState 0)
        (completedJacobiOrbit xiState n) : ℂ) =
      (canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
  have hmoment : inner ℝ (completedJacobiOrbit xiState n)
      (completedJacobiOrbit xiState 0) = moments n := by
    simpa only [completedJacobiOrbit, completedJacobiGreenJet, Nat.add_zero] using
      inner_greenJetEvenSectorJet_eq_moment
        (completedGreenJet_gramRepresentation certificate.realMomentKernel) n 0
  rw [real_inner_comm, hmoment,
    completedNativeLogDerivativeMoment_eq_canonical
      certificate.logarithmicMoments]

set_option maxHeartbeats 150000 in
set_option synthInstance.maxHeartbeats 300000 in
/-- Concrete complex graph-resolvent germ of the completed positive Green
operator.  The certificate contains one analytic graph-valued function, its
exact resolvent equation, and its native logarithmic-derivative readout. -/
def completedJacobiComplexGraphResolvent_germ
    (certificate :
      CompletedNativeGreenWeylReducedHeightCertificate xiState moments) :
    GermCertificate (E := CompletedJacobiEvenCarrier xiState)
      (completedJacobiEnergyOperator certificate)
      (ofReal (E := CompletedJacobiEvenCarrier xiState)
        (completedJacobiOrbit xiState 0))
  completedNativeLogDerivative :=
  germCertificate_of_orbit
    (E := CompletedJacobiEvenCarrier xiState)
    (completedJacobiEnergyOperator certificate)
    (by
      unfold completedJacobiEnergyOperator
      exact closedGreenJetEnergyAdjointSquare_isClosed
        (completedGreenJet_gramRepresentation certificate.realMomentKernel)
        (completedGreenJet_even_linearIndependent certificate.evenIndependent)
        (completedGreenJet_odd_linearIndependent certificate.oddIndependent))
    (v := completedJacobiOrbit xiState)
    (coeff := fun n =>
      (canonicalCompletedNativeLogDerivativeMoment n : ℂ))
    (f := completedNativeLogDerivative)
    (completedJacobiOrbit_geometricBound
      (xiState := xiState) (moments := moments) certificate)
    (completedJacobiOrbit_isOperatorOrbit
      (xiState := xiState) (moments := moments) certificate)
    (completedJacobiOrbit_head_inner_eq_canonicalMoment
      (xiState := xiState) (moments := moments) certificate)
    completedNativeLogDerivative_eventually_hasSum_canonical

set_option maxHeartbeats 200000 in
/-- The same concrete graph-resolvent germ in the signed-height coordinate.
Its scalar readout is the canonical global Weyl continuation near the center,
while the vector equation keeps the exact positive parameter `z^2`. -/
def completedJacobiComplexGraphResolvent_heightGerm
    (certificate :
      CompletedNativeGreenWeylReducedHeightCertificate xiState moments) :
    HeightGermCertificate (E := CompletedJacobiEvenCarrier xiState)
      (completedJacobiEnergyOperator certificate)
      (ofReal (E := CompletedJacobiEvenCarrier xiState)
        (completedJacobiOrbit xiState 0))
      completedNativeJacobiWeylHeightContinuation :=
  certificate.completedJacobiComplexGraphResolvent_germ
    |>.squareReparameterization
    |>.congrScalar
      completedNativeJacobiWeylHeightContinuation_eventuallyEq_reducedLogDerivative_sq.symm

end CompletedNativeGreenWeylReducedHeightCertificate

end

end CarrySelfAdjointOperator
