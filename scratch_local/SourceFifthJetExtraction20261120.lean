import scratch_local.NativeSchurJetConvolution20261120
import scratch_local.SourceReductionParityStageFour20261120
import Mathlib.Tactic
namespace CarrySelfAdjointOperator.SourcePositiveReduction
#check greenTaylorJet_mul
#check chainResponse_four_zero

open Filter Topology
noncomputable section

/-- The exact source-derived S-fraction recursion for the *analytic axes*,
including j=3 -> j=4. This is a genuine equality of germs, not a
postulated algebraic moment recursion. -/
theorem chainAxis_step_germ (j : ℕ) (hj : j < 4) :
    (fun z : ℂ => chainAxis j z) =ᶠ[nhds 0]
    (fun z : ℂ => (chainScale j : ℂ) +
       (chainScale j : ℂ) * z^2 * chainAxis j z * chainAxis (j+1) z) := by
  rcases chain_first_four_regular_local with ⟨U, hUopen, hzeroU, hreg⟩
  have hU : U ∈ nhds (0 : ℂ) := hUopen.mem_nhds hzeroU
  filter_upwards [hU] with z hz
  have haxis : chainAxis j z ≠ 0 := hreg z hz j hj
  have h0 := chain_first_five_centers j (by omega)
  have h1 := chain_first_five_centers (j+1) (by omega)
  have ha := chain_first_four_real_scales j hj
  have hp := chain_first_four_scales_pos j hj
  have h := chainReduction_source_equation j h0 ha hp z haxis
  rw [chainResponse_eq_mul_axis j h0,
      chainResponse_eq_mul_axis (j+1) h1] at h
  have ha0 : (chainScale j : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hmul :
      (chainScale j : ℂ) *
        ((z * chainAxis j z) * (z * chainAxis (j+1) z)) =
      chainAxis j z - (chainScale j : ℂ) := by
    calc
      _ = (chainScale j : ℂ) *
          (chainAxis j z / (chainScale j : ℂ) - 1) := by rw [h]
      _ = _ := by field_simp [ha0]
  linear_combination -hmul


/-- All five analytic axes inherit even parity from the ORIGINAL completed
source response. The fifth axis is treated without assuming its sign. -/
theorem chainAxis_even_lt_five (j : ℕ) (hj : j < 5) :
    (fun z => chainAxis j (-z)) =ᶠ[nhds 0] (chainAxis j) := by
  change (fun z => dslope (chainResponse j) 0 (-z)) =ᶠ[nhds 0]
    (dslope (chainResponse j) 0)
  interval_cases j
  · exact dslope_even_of_odd_germ sourceResponse
      sourceResponse_zero completedSourceResponse_eventually_odd
  · apply dslope_even_of_odd_germ (chainResponse 1)
    · rw [chainResponse_one_eq]
      exact reducedResponse_zero
    · exact chainResponse_one_odd
  · apply dslope_even_of_odd_germ (chainResponse 2)
    · rw [chainResponse_two_eq]
      exact secondReducedResponse_zero
    · exact chainResponse_two_odd
  · exact dslope_even_of_odd_germ (chainResponse 3)
      chainResponse_three_zero chainResponse_three_odd
  · exact dslope_even_of_odd_germ (chainResponse 4)
      chainResponse_four_zero chainResponse_four_odd

theorem chainAxis_analytic_lt_five (j : ℕ) (hj : j < 5) :
    AnalyticAt ℂ (chainAxis j) 0 := by
  interval_cases j
  · have heq : chainAxis 0 = sourceAxis := funext chainAxis_zero_eq
    rw [heq]
    exact sourceAxis_analyticAt_zero
  · have heq : chainAxis 1 = secondAxis := funext chainAxis_one_eq
    rw [heq]
    exact secondAxis_analyticAt_zero
  · exact chainAxis_two_analyticAt_zero
  · exact chainAxis_three_analyticAt_zero
  · exact chainAxis_four_analyticAt_zero

/-- Exact parity of the source-derived Taylor coefficients. -/
theorem greenTaylorJet_even_odd_zero
    (f : ℂ → ℂ)
    (hEven : (fun z => f (-z)) =ᶠ[nhds 0] f)
    (n : ℕ) :
    completedGreenTaylorJet f (2*n+1) = 0 := by
  have h := hEven.iteratedDeriv_eq (2*n+1)
  rw [iteratedDeriv_comp_neg] at h
  have hpow : (-1 : ℂ) ^ (2*n+1) = -1 := by
    simp [pow_add, pow_mul]
  rw [hpow] at h
  simp only [neg_zero, neg_one_smul] at h
  have hh : iteratedDeriv (2*n+1) f 0 = 0 := by
    linear_combination -h / 2
  unfold completedGreenTaylorJet
  rw [hh]
  simp

theorem chainAxis_oddTaylor_zero (j : ℕ) (hj : j < 5) (n : ℕ) :
    completedGreenTaylorJet (chainAxis j) (2*n+1) = 0 :=
  greenTaylorJet_even_odd_zero (chainAxis j)
    (chainAxis_even_lt_five j hj) n


/-- Multiplication by z² shifts the analytic jet by exactly two orders. -/
theorem greenTaylorJet_zsq_mul
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    completedGreenTaylorJet (fun z : ℂ => z^2 * f z) (n+2) =
      completedGreenTaylorJet f n := by
  have heq : (fun z : ℂ => z^2 * f z) =
      (fun z : ℂ => z * (z * f z)) := by
    funext z
    ring
  rw [heq]
  calc
    _ = completedGreenTaylorJet (fun z : ℂ => z * f z) (n+1) := by
      simpa [Nat.add_assoc] using
        greenTaylorJet_z_mul (fun z : ℂ => z * f z)
          (analyticAt_id.mul hf) (n+1)
    _ = completedGreenTaylorJet f n :=
      greenTaylorJet_z_mul f hf n

theorem greenTaylorJet_add
    (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    completedGreenTaylorJet (f+g) n =
      completedGreenTaylorJet f n + completedGreenTaylorJet g n := by
  unfold completedGreenTaylorJet
  rw [iteratedDeriv_add (hf.contDiffAt : ContDiffAt ℂ n f 0)
    (hg.contDiffAt : ContDiffAt ℂ n g 0)]
  simp only [smul_eq_mul]
  ring

theorem greenTaylorJet_const_mul (a : ℂ)
    (f : ℂ → ℂ) (n : ℕ) :
    completedGreenTaylorJet (fun z => a * f z) n =
      a * completedGreenTaylorJet f n := by
  unfold completedGreenTaylorJet
  rw [iteratedDeriv_const_mul_field]
  simp only [smul_eq_mul]
  ring

theorem greenTaylorJet_const_succ (a : ℂ) (n : ℕ) :
    completedGreenTaylorJet (fun _ : ℂ => a) (n+1) = 0 := by
  simp [completedGreenTaylorJet, iteratedDeriv_const]

theorem greenTaylorJet_eq_of_germ
    (f g : ℂ → ℂ) (hf : f =ᶠ[nhds 0] g) (n : ℕ) :
    completedGreenTaylorJet f n = completedGreenTaylorJet g n := by
  unfold completedGreenTaylorJet
  rw [hf.iteratedDeriv_eq n]


/-- Every Taylor coefficient after the constant obeys the genuine
native-source Stieltjes recursion, for all four available stages. -/
theorem chainAxis_step_jet (j : ℕ) (hj : j < 4) (n : ℕ) :
    completedGreenTaylorJet (chainAxis j) (n+2) =
      (chainScale j : ℂ) *
        ∑ i ∈ Finset.range (n+1),
          completedGreenTaylorJet (chainAxis j) i *
          completedGreenTaylorJet (chainAxis (j+1)) (n-i) := by
  let a : ℂ := chainScale j
  let f : ℂ → ℂ := chainAxis j
  let g : ℂ → ℂ := chainAxis (j+1)
  let p : ℂ → ℂ := f * g
  have hf : AnalyticAt ℂ f 0 := chainAxis_analytic_lt_five j (by omega)
  have hg : AnalyticAt ℂ g 0 := chainAxis_analytic_lt_five (j+1) (by omega)
  have hp : AnalyticAt ℂ p 0 := hf.mul hg
  have hq : AnalyticAt ℂ (fun z : ℂ => z^2 * p z) 0 :=
    (analyticAt_id.pow 2).mul hp
  have hprod : AnalyticAt ℂ (fun z : ℂ => a * (z^2 * p z)) 0 :=
    analyticAt_const.mul hq
  have hlocal : f =ᶠ[nhds 0]
      (fun z : ℂ => a + a * (z^2 * p z)) := by
    filter_upwards [chainAxis_step_germ j hj] with z hz
    dsimp [a, f, p, g]
    calc
      chainAxis j z =
          (chainScale j : ℂ) +
            (chainScale j : ℂ) * z^2 * chainAxis j z * chainAxis (j+1) z := hz
      _ = _ := by ring
  calc
    completedGreenTaylorJet f (n+2) =
        completedGreenTaylorJet (fun z : ℂ => a + a * (z^2 * p z)) (n+2) :=
      greenTaylorJet_eq_of_germ f _ hlocal (n+2)
    _ = completedGreenTaylorJet (fun _ : ℂ => a) (n+2) +
          completedGreenTaylorJet (fun z : ℂ => a * (z^2*p z)) (n+2) := by
      exact greenTaylorJet_add (fun _ : ℂ => a)
        (fun z : ℂ => a * (z^2*p z))
          analyticAt_const hprod (n+2)
    _ = a * completedGreenTaylorJet (fun z : ℂ => z^2 * p z) (n+2) := by
      rw [show n+2 = (n+1)+1 by omega,
        greenTaylorJet_const_succ, greenTaylorJet_const_mul]
      ring
    _ = a * completedGreenTaylorJet p n := by
      rw [greenTaylorJet_zsq_mul p hp n]
    _ = _ := by
      rw [greenTaylorJet_mul f g hf hg n]


/-- Source-derived coefficient in the natural squared height coordinate. -/
def evenAxisJet (j n : ℕ) : ℂ :=
  completedGreenTaylorJet (chainAxis j) (2*n)

theorem evenAxisJet_zero (j : ℕ) :
    evenAxisJet j 0 = chainAxis j 0 := by
  simp [evenAxisJet, completedGreenTaylorJet]

theorem evenAxisJet_one (j : ℕ) (hj : j < 4) :
    evenAxisJet j 1 =
      (chainScale j : ℂ) * evenAxisJet j 0 * evenAxisJet (j+1) 0 := by
  have h := chainAxis_step_jet j hj 0
  simpa [evenAxisJet, Finset.sum_range_succ, mul_assoc] using h

theorem evenAxisJet_two (j : ℕ) (hj : j < 4) :
    evenAxisJet j 2 = (chainScale j : ℂ) *
      (evenAxisJet j 0 * evenAxisJet (j+1) 1 +
       evenAxisJet j 1 * evenAxisJet (j+1) 0) := by
  have h := chainAxis_step_jet j hj 2
  have hOddj := chainAxis_oddTaylor_zero j (by omega) 0
  have hOddj1 := chainAxis_oddTaylor_zero (j+1) (by omega) 0
  simpa [evenAxisJet, Finset.sum_range_succ, hOddj, hOddj1,
    Nat.add_assoc, mul_add, add_mul] using h


theorem evenAxisJet_three (j : ℕ) (hj : j < 4) :
    evenAxisJet j 3 = (chainScale j : ℂ) *
      (evenAxisJet j 0 * evenAxisJet (j+1) 2 +
       evenAxisJet j 1 * evenAxisJet (j+1) 1 +
       evenAxisJet j 2 * evenAxisJet (j+1) 0) := by
  have h := chainAxis_step_jet j hj 4
  have h1 := chainAxis_oddTaylor_zero j (by omega) 0
  have h3 := chainAxis_oddTaylor_zero j (by omega) 1
  have hg1 := chainAxis_oddTaylor_zero (j+1) (by omega) 0
  have hg3 := chainAxis_oddTaylor_zero (j+1) (by omega) 1
  simp [evenAxisJet, Finset.sum_range_succ, h1, h3, hg1, hg3] at h ⊢
  exact h

theorem evenAxisJet_four (j : ℕ) (hj : j < 4) :
    evenAxisJet j 4 = (chainScale j : ℂ) *
      (evenAxisJet j 0 * evenAxisJet (j+1) 3 +
       evenAxisJet j 1 * evenAxisJet (j+1) 2 +
       evenAxisJet j 2 * evenAxisJet (j+1) 1 +
       evenAxisJet j 3 * evenAxisJet (j+1) 0) := by
  have h := chainAxis_step_jet j hj 6
  have h1 := chainAxis_oddTaylor_zero j (by omega) 0
  have h3 := chainAxis_oddTaylor_zero j (by omega) 1
  have h5 := chainAxis_oddTaylor_zero j (by omega) 2
  have hg1 := chainAxis_oddTaylor_zero (j+1) (by omega) 0
  have hg3 := chainAxis_oddTaylor_zero (j+1) (by omega) 1
  have hg5 := chainAxis_oddTaylor_zero (j+1) (by omega) 2
  simp [evenAxisJet, Finset.sum_range_succ, h1, h3, h5, hg1, hg3, hg5] at h ⊢
  exact h


theorem evenAxisJet_initial_coefficient (j : ℕ) (hj : j < 4) :
    evenAxisJet j 0 = (chainScale j : ℂ) := by
  rw [evenAxisJet_zero]
  exact chain_first_four_real_scales j hj

/-- The second native reduced moment already equals its S-fraction
polynomial without imposing any numerical height. -/
theorem nativeAxis_evenJet_two_polynomial :
    evenAxisJet 0 2 =
       (chainScale 0 : ℂ)^2 * (chainScale 1 : ℂ)^2 *
         ((chainScale 0 : ℂ) + (chainScale 2 : ℂ)) := by
  rw [evenAxisJet_two 0 (by decide), evenAxisJet_one 0 (by decide),
    evenAxisJet_one 1 (by decide)]
  rw [evenAxisJet_initial_coefficient 0 (by decide),
      evenAxisJet_initial_coefficient 1 (by decide),
      evenAxisJet_initial_coefficient 2 (by decide)]
  ring


/-- The actual fourth even-axis Taylor coefficient of the completed C3
source, expressed by the five source-generated continued-fraction entries.
The final entry is the COMPLEX jet, not its real part. No sign is assumed. -/
theorem nativeAxis_evenJet_four_polynomial :
    let a : ℂ := chainScale 0
    let b : ℂ := chainScale 1
    let c : ℂ := chainScale 2
    let d : ℂ := chainScale 3
    let e : ℂ := chainAxis 4 0
    evenAxisJet 0 4 =
      a^2*b^2*
      (a^3*b^2+3*a^2*b^2*c+3*a*b^2*c^2+2*a*b*c^2*d+
        b^2*c^3+2*b*c^3*d+c^3*d^2+c^2*d^2*e) := by
  dsimp only
  simp only [evenAxisJet_four 0 (by decide),
    evenAxisJet_three 0 (by decide),
    evenAxisJet_three 1 (by decide),
    evenAxisJet_two 0 (by decide),
    evenAxisJet_two 1 (by decide),
    evenAxisJet_two 2 (by decide),
    evenAxisJet_one 0 (by decide),
    evenAxisJet_one 1 (by decide),
    evenAxisJet_one 2 (by decide),
    evenAxisJet_one 3 (by decide),
    evenAxisJet_initial_coefficient 0 (by decide),
    evenAxisJet_initial_coefficient 1 (by decide),
    evenAxisJet_initial_coefficient 2 (by decide),
    evenAxisJet_initial_coefficient 3 (by decide),
    evenAxisJet_zero 4]
  ring


/-- The analytic axis of the ORIGINAL source, before any Jacobi fitting,
has exactly the canonical native moment coefficients in the variable z². -/
theorem evenAxisJet_zero_eq_nativeMoment (n : ℕ) :
    evenAxisJet 0 n =
      (canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
  have he : chainAxis 0 = sourceAxis := funext chainAxis_zero_eq
  have hr : (fun z : ℂ => z * sourceAxis z) = sourceResponse := by
    funext z
    exact (sourceResponse_eq_mul_axis z).symm
  have h := greenTaylorJet_z_mul sourceAxis sourceAxis_analyticAt_zero (2*n)
  rw [hr] at h
  have ht := sourceResponse_taylor (2*n+1)
  rw [completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical n] at ht
  rw [evenAxisJet, he]
  exact h.symm.trans ht


theorem nativeAxis_evenJet_zero_polynomial :
    evenAxisJet 0 0 = (chainScale 0 : ℂ) :=
  evenAxisJet_initial_coefficient 0 (by decide)

theorem nativeAxis_evenJet_one_polynomial :
    evenAxisJet 0 1 = (chainScale 0 : ℂ)^2 * (chainScale 1 : ℂ) := by
  rw [evenAxisJet_one 0 (by decide),
    evenAxisJet_initial_coefficient 0 (by decide),
    evenAxisJet_initial_coefficient 1 (by decide)]
  ring

theorem nativeAxis_evenJet_three_polynomial :
    let a : ℂ := chainScale 0
    let b : ℂ := chainScale 1
    let c : ℂ := chainScale 2
    let d : ℂ := chainScale 3
    evenAxisJet 0 3 =
      a^2*b^2*(a^2*b+2*a*b*c+b*c^2+c^2*d) := by
  dsimp only
  simp only [evenAxisJet_three 0 (by decide),
    evenAxisJet_two 0 (by decide),
    evenAxisJet_two 1 (by decide),
    evenAxisJet_one 0 (by decide),
    evenAxisJet_one 1 (by decide),
    evenAxisJet_one 2 (by decide),
    evenAxisJet_initial_coefficient 0 (by decide),
    evenAxisJet_initial_coefficient 1 (by decide),
    evenAxisJet_initial_coefficient 2 (by decide),
    evenAxisJet_initial_coefficient 3 (by decide)]
  ring


local notation "m" => canonicalCompletedNativeLogDerivativeMoment

/-- Exact native even and shifted Hankel minors, before sign interpretation. -/
def nativeD2 : ℂ := (m 0 : ℂ)*(m 2 : ℂ)-(m 1 : ℂ)^2
def nativeOddD2 : ℂ := (m 1 : ℂ)*(m 3 : ℂ)-(m 2 : ℂ)^2
def nativeD3 : ℂ :=
  (m 0 : ℂ)*(m 2 : ℂ)*(m 4 : ℂ) +
    2*(m 1 : ℂ)*(m 2 : ℂ)*(m 3 : ℂ) -
    (m 0 : ℂ)*(m 3 : ℂ)^2 -
    (m 1 : ℂ)^2*(m 4 : ℂ) -
    (m 2 : ℂ)^3

theorem nativeD2_source_factors :
    nativeD2 = (chainScale 0 : ℂ)^3 * (chainScale 1 : ℂ)^2 *
      (chainScale 2 : ℂ) := by
  unfold nativeD2
  rw [← evenAxisJet_zero_eq_nativeMoment 0,
    ← evenAxisJet_zero_eq_nativeMoment 1,
    ← evenAxisJet_zero_eq_nativeMoment 2,
    nativeAxis_evenJet_zero_polynomial,
    nativeAxis_evenJet_one_polynomial,
    nativeAxis_evenJet_two_polynomial]
  ring

theorem nativeOddD2_source_factors :
    nativeOddD2 = (chainScale 0 : ℂ)^4 * (chainScale 1 : ℂ)^3 *
      (chainScale 2 : ℂ)^2 * (chainScale 3 : ℂ) := by
  unfold nativeOddD2
  rw [← evenAxisJet_zero_eq_nativeMoment 1,
    ← evenAxisJet_zero_eq_nativeMoment 2,
    ← evenAxisJet_zero_eq_nativeMoment 3,
    nativeAxis_evenJet_one_polynomial,
    nativeAxis_evenJet_two_polynomial,
    nativeAxis_evenJet_three_polynomial]
  ring

set_option maxHeartbeats 2000000 in
theorem nativeD3_source_factors :
    nativeD3 = (chainScale 0 : ℂ)^5 * (chainScale 1 : ℂ)^4 *
      (chainScale 2 : ℂ)^3 * (chainScale 3 : ℂ)^2 *
      chainAxis 4 0 := by
  unfold nativeD3
  rw [← evenAxisJet_zero_eq_nativeMoment 0,
    ← evenAxisJet_zero_eq_nativeMoment 1,
    ← evenAxisJet_zero_eq_nativeMoment 2,
    ← evenAxisJet_zero_eq_nativeMoment 3,
    ← evenAxisJet_zero_eq_nativeMoment 4,
    nativeAxis_evenJet_zero_polynomial,
    nativeAxis_evenJet_one_polynomial,
    nativeAxis_evenJet_two_polynomial,
    nativeAxis_evenJet_three_polynomial,
    nativeAxis_evenJet_four_polynomial]
  ring


theorem nativeOddD2_ne_zero : nativeOddD2 ≠ 0 := by
  rw [nativeOddD2_source_factors]
  have h0 : (chainScale 0 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (chain_first_four_scales_pos 0 (by decide)).ne'
  have h1 : (chainScale 1 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (chain_first_four_scales_pos 1 (by decide)).ne'
  have h2 : (chainScale 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (chain_first_four_scales_pos 2 (by decide)).ne'
  have h3 : (chainScale 3 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (chain_first_four_scales_pos 3 (by decide)).ne'
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (pow_ne_zero _ h0) (pow_ne_zero _ h1))
        (pow_ne_zero _ h2)) h3

/-- FULL ANALYTIC IDENTIFICATION, not a conditional hTaylor: the first
unreduced source jet is an exact quotient of its canonical Hankel minors.
All earlier scales and coefficients originate from the actual C3 source. -/
theorem chainAxis_four_eq_native_det_ratio :
    chainAxis 4 0 = nativeD2 * nativeD3 / nativeOddD2^2 := by
  apply (eq_div_iff (pow_ne_zero 2 nativeOddD2_ne_zero)).2
  rw [nativeD2_source_factors, nativeD3_source_factors,
      nativeOddD2_source_factors]
  ring

def nativeD2Real : ℝ := m 0*m 2-(m 1)^2
def nativeOddD2Real : ℝ := m 1*m 3-(m 2)^2
def nativeD3Real : ℝ :=
  m 0*m 2*m 4+2*m 1*m 2*m 3-
    m 0*(m 3)^2-(m 1)^2*m 4-(m 2)^3

private theorem nativeD2_eq_cast : nativeD2 = (nativeD2Real : ℂ) := by
  unfold nativeD2 nativeD2Real
  push_cast
  ring

private theorem nativeOddD2_eq_cast : nativeOddD2 = (nativeOddD2Real : ℂ) := by
  unfold nativeOddD2 nativeOddD2Real
  push_cast
  ring

private theorem nativeD3_eq_cast : nativeD3 = (nativeD3Real : ℂ) := by
  unfold nativeD3 nativeD3Real
  push_cast
  ring

/-- The native analytic fifth coefficient is REAL and is precisely the
canonical third-even-Hankel determinant ratio. No sign of that determinant
is presupposed here. -/
theorem chainScale_four_eq_native_det_ratio :
    chainScale 4 = nativeD2Real * nativeD3Real / nativeOddD2Real^2 := by
  have he := chainAxis_four_eq_native_det_ratio
  rw [nativeD2_eq_cast, nativeOddD2_eq_cast, nativeD3_eq_cast] at he
  have hcast :
      (nativeD2Real : ℂ) * nativeD3Real / (nativeOddD2Real : ℂ)^2 =
        ((nativeD2Real * nativeD3Real / nativeOddD2Real^2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast] at he
  have hre := congrArg Complex.re he
  simpa only [chainAxis_four_realPart_eq_scale, Complex.ofReal_re] using hre

end
end CarrySelfAdjointOperator.SourcePositiveReduction
