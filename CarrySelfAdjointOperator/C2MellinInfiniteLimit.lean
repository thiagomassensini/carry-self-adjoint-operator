import CarrySelfAdjointOperator.C2MellinComplexBridge
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Set MeasureTheory Filter Complex
open scoped Topology

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Camera

noncomputable section
set_option autoImplicit false

/-- Closed form of the infinite positive cell density, keeping its seed
separate from the geometric C2 cell contribution. -/
def nativeC2MellinGeometricOmega0 (x : ℝ) : ℝ :=
  Real.exp (-4 * x) * (4 * Real.sinh (x / 2) ^ 2) /
    (1 - Real.exp (-4 * x))

def nativeC2MellinGeometricDensity (x : ℝ) : ℝ :=
  Real.exp (-x) + nativeC2MellinGeometricOmega0 x

def nativeC2MellinComplexGeometricSourceIntegrand (s : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (s - 1) * (nativeC2MellinGeometricDensity x : ℂ)

theorem nativeC2MellinGeometricOmega0_eq_q_form {x : ℝ} (hx : 0 < x) :
    nativeC2MellinGeometricOmega0 x =
      let q := Real.exp (-x)
      q ^ 3 * (1 - q) / ((1 + q) * (1 + q ^ 2)) := by
  let q : ℝ := Real.exp (-x)
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hq4 : Real.exp (-4 * x) = q ^ 4 := by
    dsimp [q]
    calc
      Real.exp (-4 * x) = Real.exp (4 * (-x)) := by congr 1; ring
      _ = Real.exp (-x) ^ 4 := Real.exp_nat_mul _ _
      _ = _ := rfl
  have hmul : Real.exp x * q = 1 := by
    dsimp [q]
    rw [← Real.exp_add]
    norm_num
  have hexp : Real.exp x = q⁻¹ := by
    calc
      Real.exp x = Real.exp x * (q * q⁻¹) := by rw [mul_inv_cancel₀ hq0.ne']; ring
      _ = (Real.exp x * q) * q⁻¹ := by ring
      _ = q⁻¹ := by rw [hmul]; ring
  have hkernel : 4 * Real.sinh (x / 2) ^ 2 = q⁻¹ - 2 + q := by
    have h := nativeC2MellinCellKernel_eq_centered_exponentials 0 x
    simpa [q, hexp] using h
  have hden : 0 < 1 - q ^ 4 := by
    have hfactor : 1 - q ^ 4 = (1 - q) * (1 + q) * (1 + q ^ 2) := by ring
    rw [hfactor]
    positivity
  change Real.exp (-4 * x) * (4 * Real.sinh (x / 2) ^ 2) /
      (1 - Real.exp (-4 * x)) = q ^ 3 * (1 - q) /
        ((1 + q) * (1 + q ^ 2))
  rw [hq4, hkernel]
  field_simp [ne_of_gt hq0, ne_of_gt hden]
  ring

theorem nativeC2MellinGeometricOmega0_pos {x : ℝ} (hx : 0 < x) :
    0 < nativeC2MellinGeometricOmega0 x := by
  rw [nativeC2MellinGeometricOmega0_eq_q_form hx]
  dsimp
  have hq0 : 0 < Real.exp (-x) := Real.exp_pos _
  have hq1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  positivity

theorem nativeC2MellinGeometricOmega0_le_exp_neg {x : ℝ} (hx : 0 < x) :
    nativeC2MellinGeometricOmega0 x ≤ Real.exp (-x) := by
  rw [nativeC2MellinGeometricOmega0_eq_q_form hx]
  dsimp
  let q : ℝ := Real.exp (-x)
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hnum : q ^ 3 * (1 - q) ≤ q := by
    calc
      q ^ 3 * (1 - q) ≤ q ^ 3 :=
        mul_le_of_le_one_right (by positivity) (by linarith)
      _ = q ^ 2 * q := by ring
      _ ≤ 1 * q := mul_le_mul_of_nonneg_right (by nlinarith) hq0.le
      _ = q := by ring
  have hden : 1 ≤ (1 + q) * (1 + q ^ 2) := by nlinarith
  have hden0 : 0 < (1 + q) * (1 + q ^ 2) := by positivity
  rw [div_le_iff₀ hden0]
  have hmul : q ≤ q * ((1 + q) * (1 + q ^ 2)) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hden hq0.le
  exact hnum.trans hmul

theorem nativeC2MellinGeometricDensity_le_two_exp_neg {x : ℝ}
    (hx : 0 < x) :
    nativeC2MellinGeometricDensity x ≤ 2 * Real.exp (-x) := by
  unfold nativeC2MellinGeometricDensity
  have h := nativeC2MellinGeometricOmega0_le_exp_neg hx
  linarith

private theorem nativeC2MellinComplexFiniteHead_eq_geometricDensityHead
    (M : ℕ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    nativeC2MellinComplexFiniteHeadIntegrand M s x =
      (x : ℂ) ^ (s - 1) *
        ((Real.exp (-x) +
          (1 - Real.exp (-((4 : ℝ) * (M : ℝ) * x))) *
            nativeC2MellinGeometricOmega0 x : ℝ) : ℂ) := by
  rw [nativeC2MellinComplexFiniteHeadIntegrand_eq_closed_form M s hx]
  simp only [nativeC2MellinGeometricOmega0, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_exp]

private theorem nativeC2MellinComplexFiniteHead_norm_bound
    {s : ℂ} (M : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖nativeC2MellinComplexFiniteHeadIntegrand M s x‖ ≤
      2 * (Real.exp (-x) * x ^ (s.re - 1)) := by
  rw [nativeC2MellinComplexFiniteHead_eq_geometricDensityHead M s hx]
  let a : ℝ := 1 - Real.exp (-((4 : ℝ) * (M : ℝ) * x))
  have ha0 : 0 ≤ a := by
    dsimp [a]
    have harg : -((4 : ℝ) * (M : ℝ) * x) ≤ 0 :=
      neg_nonpos.mpr (by positivity)
    have he : Real.exp (-((4 : ℝ) * (M : ℝ) * x)) ≤ 1 :=
      Real.exp_le_one_iff.mpr harg
    linarith
  have ha1 : a ≤ 1 := by
    dsimp [a]
    linarith [Real.exp_pos (-((4 : ℝ) * (M : ℝ) * x))]
  have hw0 : 0 ≤ nativeC2MellinGeometricOmega0 x :=
    (nativeC2MellinGeometricOmega0_pos hx).le
  have hwle : nativeC2MellinGeometricOmega0 x ≤ Real.exp (-x) :=
    nativeC2MellinGeometricOmega0_le_exp_neg hx
  have hhead0 : 0 ≤ Real.exp (-x) + a * nativeC2MellinGeometricOmega0 x := by
    positivity
  have hheadle : Real.exp (-x) + a * nativeC2MellinGeometricOmega0 x ≤
      2 * Real.exp (-x) := by
    have hprod : a * nativeC2MellinGeometricOmega0 x ≤
        nativeC2MellinGeometricOmega0 x := by
      calc
        _ ≤ 1 * nativeC2MellinGeometricOmega0 x :=
          mul_le_mul_of_nonneg_right ha1 hw0
        _ = _ := by ring
    linarith
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_of_nonneg hhead0]
  calc
    x ^ (s.re - 1) *
        (Real.exp (-x) + a * nativeC2MellinGeometricOmega0 x) ≤
      x ^ (s.re - 1) * (2 * Real.exp (-x)) :=
        mul_le_mul_of_nonneg_left hheadle (Real.rpow_nonneg hx.le _)
    _ = 2 * (Real.exp (-x) * x ^ (s.re - 1)) := by ring

private theorem nativeC2MellinComplexFiniteHead_aestronglyMeasurable
    (M : ℕ) (s : ℂ) :
    AEStronglyMeasurable (nativeC2MellinComplexFiniteHeadIntegrand M s)
      (volume.restrict (Ioi 0)) := by
  have hpow : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (s - 1)) (Ioi 0) :=
    continuousOn_of_forall_continuousAt fun x hx =>
      (continuousAt_cpow_const (ofReal_mem_slitPlane.2 hx)).comp
        continuous_ofReal.continuousAt
  have hcont : ContinuousOn
      (nativeC2MellinComplexFiniteHeadIntegrand M s) (Ioi 0) := by
    unfold nativeC2MellinComplexFiniteHeadIntegrand nativeC2MellinComplexRateIntegrand
    refine (hpow.mul ?_).add ?_
    · fun_prop
    · apply continuousOn_finsetSum
      intro i hi
      exact hpow.mul (by fun_prop)
  exact hcont.aestronglyMeasurable measurableSet_Ioi

private theorem nativeC2MellinComplexRateMajorant_integrable {s : ℂ}
    (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => 2 * (Real.exp (-x) * x ^ (s.re - 1)))
      (Ioi 0) := by
  exact (Real.GammaIntegral_convergent hs).const_mul 2

private theorem nativeC2MellinComplexFiniteHead_tendsto_pointwise
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun M : ℕ => nativeC2MellinComplexFiniteHeadIntegrand M s x)
      atTop (𝓝 (nativeC2MellinComplexGeometricSourceIntegrand s x)) := by
  have harg : Tendsto (fun M : ℕ => -((4 : ℝ) * (M : ℝ) * x)) atTop atBot := by
    have hpos : 0 < 4 * x := by positivity
    have hmul : Tendsto (fun M : ℕ => (4 * x) * (M : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hpos
    have hneg : Tendsto (fun M : ℕ => -((4 * x) * (M : ℝ))) atTop atBot :=
      tendsto_neg_atTop_atBot.comp hmul
    convert hneg using 1
    ext M
    ring
  have hexp : Tendsto (fun M : ℕ => Real.exp (-((4 : ℝ) * (M : ℝ) * x)))
      atTop (𝓝 0) := by
    exact Real.tendsto_exp_atBot.comp harg
  have hcoef : Tendsto
      (fun M : ℕ => 1 - Real.exp (-((4 : ℝ) * (M : ℝ) * x))) atTop (𝓝 1) := by
    simpa using
      (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) from tendsto_const_nhds).sub hexp
  have hdensity : Tendsto
      (fun M : ℕ => Real.exp (-x) +
        (1 - Real.exp (-((4 : ℝ) * (M : ℝ) * x))) *
          nativeC2MellinGeometricOmega0 x)
      atTop (𝓝 (nativeC2MellinGeometricDensity x)) := by
    simpa [nativeC2MellinGeometricDensity] using
      tendsto_const_nhds.add (hcoef.mul_const (nativeC2MellinGeometricOmega0 x))
  have hcast := Complex.continuous_ofReal.continuousAt.tendsto.comp hdensity
  have hpow : Tendsto (fun _ : ℕ => (x : ℂ) ^ (s - 1)) atTop
      (𝓝 ((x : ℂ) ^ (s - 1))) := tendsto_const_nhds
  have hprod := hpow.mul hcast
  have heq : ∀ M : ℕ,
      nativeC2MellinComplexFiniteHeadIntegrand M s x =
        (x : ℂ) ^ (s - 1) *
          ((Real.exp (-x) +
            (1 - Real.exp (-((4 : ℝ) * (M : ℝ) * x))) *
              nativeC2MellinGeometricOmega0 x : ℝ) : ℂ) := by
    intro M
    exact nativeC2MellinComplexFiniteHead_eq_geometricDensityHead M s hx
  have hsequence :
      (fun M : ℕ => nativeC2MellinComplexFiniteHeadIntegrand M s x) =
      (fun M : ℕ => (x : ℂ) ^ (s - 1) *
        ((Real.exp (-x) +
          (1 - Real.exp (-((4 : ℝ) * (M : ℝ) * x))) *
            nativeC2MellinGeometricOmega0 x : ℝ) : ℂ)) := funext heq
  rw [hsequence]
  simpa [nativeC2MellinComplexGeometricSourceIntegrand,
    nativeC2MellinGeometricDensity] using hprod

/-- Dominated convergence for the finite positive C2 Mellin heads. The
majorant is `2 exp(-x) x^(Re(s)-1)`, whose integrability is exactly Euler's
Gamma integral for `Re(s)>0`. -/
theorem nativeC2MellinComplexFiniteHeadIntegral_tendsto_source
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun M : ℕ => ∫ x in Ioi (0 : ℝ),
        nativeC2MellinComplexFiniteHeadIntegrand M s x)
      atTop
      (𝓝 (∫ x in Ioi (0 : ℝ), nativeC2MellinComplexGeometricSourceIntegrand s x)) := by
  apply tendsto_integral_of_dominated_convergence
    (bound := fun x => 2 * (Real.exp (-x) * x ^ (s.re - 1)))
  · exact fun M => nativeC2MellinComplexFiniteHead_aestronglyMeasurable M s
  · exact nativeC2MellinComplexRateMajorant_integrable hs
  · intro M
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact nativeC2MellinComplexFiniteHead_norm_bound M hx
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact nativeC2MellinComplexFiniteHead_tendsto_pointwise s hx

/-- The infinite positive hyperbolic C2 source has Mellin transform equal to
the original infinite bracket characteristic. This is derived by dominated
convergence from the finite positive cells and the existing finite-head
series limit. -/
theorem nativeC2MellinComplexGeometricSourceIntegral_eq_gamma_bracketCharacteristic
    {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (0 : ℝ), nativeC2MellinComplexGeometricSourceIntegrand s x) =
      Complex.Gamma s * bracketCharacteristic 2 s := by
  have hsource := nativeC2MellinComplexFiniteHeadIntegral_tendsto_source hs
  have hgamma : Tendsto (fun _ : ℕ => Complex.Gamma s) atTop
      (𝓝 (Complex.Gamma s)) := tendsto_const_nhds
  have hseries := hgamma.mul
    (finiteBracketCharacteristic_tendsto (by norm_num : 2 ≤ 2)
      (by linarith : -1 < s.re))
  have hseq :
      (fun M : ℕ => ∫ x in Ioi (0 : ℝ),
        nativeC2MellinComplexFiniteHeadIntegrand M s x) =
      (fun M => Complex.Gamma s * finiteBracketCharacteristic 2 M s) := by
    funext M
    exact nativeC2MellinComplexFiniteHeadIntegral hs M
  rw [hseq] at hsource
  exact tendsto_nhds_unique hsource hseries

end

end CarrySelfAdjointOperator
