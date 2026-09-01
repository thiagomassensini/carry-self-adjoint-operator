import CarrySelfAdjointOperator.CompletedNativeXiCosineKernel
import CarrySelfAdjointOperator.CompletedGreenJetCoefficientRecurrence
import Mathlib.Analysis.MellinInversion
import Mathlib.Tactic

/-!
# The centered theta--cosine representation of the completed characteristic

This module derives the centered Fourier representation directly from
Mathlib's Mellin construction of `completedRiemannZeta₀`.  The logarithmic
change of variables produces the real theta tail

`A(u) = exp(u/2) (theta(exp(2u)) - 1)`.

The modified Mellin profile is even (away from its deliberately changed
value at the single point `u = 0`), so its full Fourier transform is twice a
half-line cosine transform.  Combining this with the two polar correction
terms in `completedRiemannZeta_eq` gives the exact identity

`Xi(t) = 1/2 - (t² + 1/4) ∫₀∞ A(u) cos(tu) du`.

The downstream integration-by-parts module identifies the right-hand side
with the cosine transform of the positive explicit kernel fixed in
`CompletedNativeXiCosineKernel`.
-/

open Real Complex Set MeasureTheory
open scoped FourierTransform

namespace CarrySelfAdjointOperator

namespace XiThetaCosine

noncomputable section

private theorem exp_neg_deriv (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Real.exp (-y)) (-Real.exp (-x)) x := by
  simpa [Function.comp_def] using
    (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)

private theorem exp_neg_image :
    (fun x : ℝ ↦ Real.exp (-x)) '' Set.univ = Set.Ioi 0 := by
  rw [Set.image_univ]
  ext y
  simp only [Set.mem_range, Set.mem_Ioi]
  constructor
  · rintro ⟨x, rfl⟩
    exact Real.exp_pos _
  · intro hy
    refine ⟨-Real.log y, ?_⟩
    simp [Real.exp_log hy]

private theorem exp_neg_inj :
    Set.InjOn (fun x : ℝ ↦ Real.exp (-x)) Set.univ :=
  Real.exp_injective.injOn.comp neg_injective.injOn (Set.mapsTo_univ _ _)

theorem mellinConvergent_ofReal_iff_integrable_logProfile
    (f : ℝ → ℂ) (sigma : ℝ) :
    MellinConvergent f (sigma : ℂ) ↔
      Integrable (fun u : ℝ ↦
        (Real.exp (-sigma * u) : ℂ) * f (Real.exp (-u))) := by
  rw [MellinConvergent, ← exp_neg_image]
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ
    (fun x _ ↦ (exp_neg_deriv x).hasDerivWithinAt)
    exp_neg_inj]
  rw [integrableOn_univ]
  apply integrable_congr
  filter_upwards [] with u
  simp only [abs_neg, abs_of_pos (Real.exp_pos _), smul_eq_mul]
  rw [show (sigma : ℂ) - 1 = ((sigma - 1 : ℝ) : ℂ) by push_cast; ring]
  rw [← Complex.ofReal_cpow (Real.exp_pos _).le]
  rw [Complex.real_smul]
  rw [← mul_assoc]
  rw [← Complex.ofReal_mul]
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
    ← Real.exp_add]
  congr 2
  ring

def p := HurwitzZeta.hurwitzEvenFEPair 0

def profile (u : ℝ) : ℂ :=
  (Real.exp (u / 2) : ℂ) * p.f_modif (Real.exp (2 * u))

def thetaTail (u : ℝ) : ℝ :=
  Real.exp (u / 2) *
    (HurwitzZeta.evenKernel 0 (Real.exp (2 * u)) - 1)

theorem profile_of_pos {u : ℝ} (hu : 0 < u) :
    profile u = (thetaTail u : ℂ) := by
  have hexp : 1 < Real.exp (2 * u) := by
    rw [Real.one_lt_exp_iff]
    linarith
  have hnot : ¬ Real.exp (2 * u) < 1 := not_lt_of_ge hexp.le
  simp [profile, thetaTail, p, WeakFEPair.f_modif,
    HurwitzZeta.hurwitzEvenFEPair, Function.comp_def, hexp, hnot]

theorem p_gmodif_eq : p.g_modif = p.f_modif := by
  have h := congrArg WeakFEPair.f_modif
    HurwitzZeta.hurwitzEvenFEPair_zero_symm
  exact h

theorem integrable_profile : Integrable profile := by
  have hm := p.isStrongFEPair_toStrongFEPair.hasMellin (1 / 4 : ℂ)
  have hm' : MellinConvergent p.f_modif (1 / 4 : ℂ) := by
    simpa [WeakFEPair.toStrongFEPair] using hm.1
  have hlog : Integrable (fun x : ℝ ↦
      (Real.exp (-(1 / 4 : ℝ) * x) : ℂ) *
        p.f_modif (Real.exp (-x))) :=
    (mellinConvergent_ofReal_iff_integrable_logProfile
      p.f_modif (1 / 4 : ℝ)).mp (by simpa using hm')
  have hscaled := hlog.comp_mul_left' (by norm_num : (-2 : ℝ) ≠ 0)
  apply hscaled.congr
  filter_upwards [] with u
  rw [show -(1 / 4 : ℝ) * (-2 * u) = u / 2 by ring,
    show -(-2 * u) = 2 * u by ring]
  rfl

theorem profile_neg (u : ℝ) :
    profile (-u) = profile u := by
  have hfe := p.hf_modif_FE (Real.exp (2 * u)) (Real.exp_pos _)
  rw [p_gmodif_eq] at hfe
  have hinv : Real.exp (2 * -u) = 1 / Real.exp (2 * u) := by
    rw [show 2 * -u = -(2 * u) by ring, Real.exp_neg]
    simp [one_div]
  unfold profile
  rw [hinv, hfe]
  simp [p, HurwitzZeta.hurwitzEvenFEPair, smul_eq_mul,
    Real.rpow_def_of_pos (Real.exp_pos _)]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem integrable_oscillatory_profile (t : ℝ) :
    Integrable (fun u : ℝ ↦ Complex.exp (t * u * I) * profile u) := by
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ ↦ Complex.exp (t * u * I) * profile u) := by
    exact (by fun_prop : Continuous
      (fun u : ℝ ↦ Complex.exp (t * u * I))).aestronglyMeasurable.mul
        integrable_profile.aestronglyMeasurable
  apply (integrable_norm_iff hmeas).mp
  apply integrable_profile.norm.congr
  filter_upwards [] with u
  rw [norm_mul]
  have hnorm : ‖Complex.exp (t * u * I)‖ = 1 := by
    simpa only [Complex.ofReal_mul] using
      Complex.norm_exp_ofReal_mul_I (t * u)
  rw [hnorm, one_mul]

theorem integral_oscillatory_profile_eq_cosine (t : ℝ) :
    (∫ u : ℝ, Complex.exp (t * u * I) * profile u) =
      ((2 * ∫ u : ℝ in Ioi 0, Real.cos (t * u) * thetaTail u : ℝ) : ℂ) := by
  let F : ℝ → ℂ := fun u ↦ Complex.exp (t * u * I) * profile u
  let G : ℝ → ℂ := fun u ↦ Complex.exp ((-t) * u * I) * profile u
  have hF : Integrable F := by
    simpa [F] using integrable_oscillatory_profile t
  have hG : Integrable G := by
    simpa [G] using integrable_oscillatory_profile (-t)
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    (b := (0 : ℝ)) hF.integrableOn hF.integrableOn
  have hleft : (∫ u : ℝ in Iic 0, F u) = ∫ u : ℝ in Ioi 0, G u := by
    calc
      (∫ u : ℝ in Iic 0, F u) = ∫ u : ℝ in Ioi 0, F (-u) := by
        convert (integral_comp_neg_Ioi 0 F).symm using 1
        all_goals simp
      _ = ∫ u : ℝ in Ioi 0, G u := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        simp only [F, G]
        rw [profile_neg]
        congr 2
        push_cast
        ring
  change (∫ u : ℝ, F u) = _
  rw [← hsplit, hleft]
  rw [← integral_add hG.integrableOn hF.integrableOn]
  calc
    (∫ u : ℝ in Ioi 0, G u + F u) =
        ∫ u : ℝ in Ioi 0,
          (2 : ℂ) * (Real.cos (t * u) : ℂ) * profile u := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _hu
      simp only [F, G]
      have hnegexp : Complex.exp (-↑t * ↑u * I) =
          (Real.cos (t * u) : ℂ) - (Real.sin (t * u) : ℂ) * I := by
        rw [show -↑t * ↑u * I = ((-t * u : ℝ) : ℂ) * I by push_cast; ring,
          Complex.exp_ofReal_mul_I,
          show -t * u = -(t * u) by ring, Real.cos_neg, Real.sin_neg]
        push_cast
        ring
      have hposexp : Complex.exp (↑t * ↑u * I) =
          (Real.cos (t * u) : ℂ) + (Real.sin (t * u) : ℂ) * I := by
        rw [show ↑t * ↑u * I = ((t * u : ℝ) : ℂ) * I by push_cast; ring,
          Complex.exp_ofReal_mul_I]
      rw [hnegexp, hposexp]
      push_cast
      ring
    _ = ∫ u : ℝ in Ioi 0,
          (2 : ℂ) * (Real.cos (t * u) : ℂ) * (thetaTail u : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      change (2 : ℂ) * (Real.cos (t * u) : ℂ) * profile u = _
      rw [profile_of_pos hu]
    _ = ((2 * ∫ u : ℝ in Ioi 0,
          Real.cos (t * u) * thetaTail u : ℝ) : ℂ) := by
      rw [show (fun u : ℝ ↦
          (2 : ℂ) * (Real.cos (t * u) : ℂ) * (thetaTail u : ℂ)) =
          fun u : ℝ ↦ (2 : ℂ) *
            ((Real.cos (t * u) * thetaTail u : ℝ) : ℂ) by
        funext u
        push_cast
        ring]
      rw [integral_const_mul]
      have hreal :
          (∫ u : ℝ in Ioi 0,
              ((Real.cos (t * u) * thetaTail u : ℝ) : ℂ)) =
            ((∫ u : ℝ in Ioi 0,
              Real.cos (t * u) * thetaTail u : ℝ) : ℂ) := by
        exact integral_ofReal
      rw [hreal]
      push_cast
      rfl

theorem zeta0_center_eq (t : ℝ) :
    completedRiemannZeta₀ ((1 / 2 : ℂ) + t * I) =
      ∫ u : ℝ, Complex.exp (t * u * I) * profile u := by
  rw [completedRiemannZeta₀, HurwitzZeta.completedHurwitzZetaEven₀,
    WeakFEPair.Λ₀, mellin_eq_fourier, Real.fourier_eq']
  let g : ℝ → ℂ := fun x ↦
      Complex.exp (↑(-2 * π * inner ℝ x
        ((((1 / 2 : ℂ) + t * I) / 2).im / (2 * π))) * I) •
        (Real.exp (-(((1 / 2 : ℂ) + t * I) / 2).re * x) •
          (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (-x)))
  change (∫ x : ℝ, g x) / 2 = _
  have hscale :
      (∫ u : ℝ, g (-2 * u)) = (1 / 2 : ℝ) • ∫ x : ℝ, g x := by
    simpa using Measure.integral_comp_mul_left g (-2)
  calc
    (∫ x : ℝ, g x) / 2 = (1 / 2 : ℝ) • ∫ x : ℝ, g x := by
      norm_num [div_eq_mul_inv, smul_eq_mul]
      rw [mul_comm]
    _ = ∫ u : ℝ, g (-2 * u) := hscale.symm
    _ = ∫ u : ℝ, Complex.exp (t * u * I) * profile u := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp [g, profile, p, smul_eq_mul]
      congr 2
      · field_simp [Real.pi_ne_zero]
      · ring

theorem zeta0_center_eq_cosine (t : ℝ) :
    completedRiemannZeta₀ ((1 / 2 : ℂ) + t * I) =
      ((2 * ∫ u : ℝ in Ioi 0,
        Real.cos (t * u) * thetaTail u : ℝ) : ℂ) :=
  (zeta0_center_eq t).trans (integral_oscillatory_profile_eq_cosine t)

theorem completedNative_eq_thetaTail_cosine (t : ℝ) :
    completedNativeOperatorCharacteristic (t : ℂ) =
      ((1 / 2 - (t ^ 2 + 1 / 4) *
        ∫ u : ℝ in Ioi 0, Real.cos (t * u) * thetaTail u : ℝ) : ℂ) := by
  have hs : operatorHeightParameter (t : ℂ) ∈
      CPFormal.Analytic.Cp.genuineCriticalStrip := by
    constructor <;> norm_num [operatorHeightParameter]
  rw [completedNativeOperatorCharacteristic_eq_completedRiemannZeta hs,
    nativeXiCompletionFactor_mul_riemannZeta_eq_regularizedCompleted hs,
    completedRiemannZeta_eq]
  rw [show operatorHeightParameter (t : ℂ) =
      (1 / 2 : ℂ) + t * I by
    simp [operatorHeightParameter]
    ring]
  have hs0 : ((1 / 2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hs1 : (1 : ℂ) - ((1 / 2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  let s : ℂ := (1 / 2 : ℂ) + t * I
  have hcancel0 : s * (1 / s) = 1 := by
    rw [one_div, mul_inv_cancel₀]
    simpa [s] using hs0
  have hcancel1 : (s - 1) * (1 / (1 - s)) = -1 := by
    have hneg : s - 1 = -(1 - s) := by ring
    rw [hneg, one_div, neg_mul, mul_inv_cancel₀]
    simpa [s] using hs1
  have hfirst : s * (s - 1) * (1 / s) = s - 1 := by
    calc
      s * (s - 1) * (1 / s) = (s * (1 / s)) * (s - 1) := by ring
      _ = s - 1 := by rw [hcancel0, one_mul]
  have hsecond : s * (s - 1) * (1 / (1 - s)) = -s := by
    calc
      s * (s - 1) * (1 / (1 - s)) =
          s * ((s - 1) * (1 / (1 - s))) := by ring
      _ = -s := by rw [hcancel1]; ring
  have hcorrection :
      (1 / 2 : ℂ) * ((1 / 2 : ℂ) + t * I) *
          ((1 / 2 : ℂ) + t * I - 1) *
          (completedRiemannZeta₀ ((1 / 2 : ℂ) + t * I) -
            1 / ((1 / 2 : ℂ) + t * I) -
            1 / (1 - ((1 / 2 : ℂ) + t * I))) =
        1 / 2 +
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) + t * I) *
            ((1 / 2 : ℂ) + t * I - 1) *
              completedRiemannZeta₀ ((1 / 2 : ℂ) + t * I) := by
    change (1 / 2 : ℂ) * s * (s - 1) *
        (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) = _
    calc
      (1 / 2 : ℂ) * s * (s - 1) *
          (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) =
          (1 / 2 : ℂ) *
            (s * (s - 1) * completedRiemannZeta₀ s -
              s * (s - 1) * (1 / s) -
              s * (s - 1) * (1 / (1 - s))) := by ring
      _ = 1 / 2 +
          (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s := by
        rw [hfirst, hsecond]
        ring
  rw [hcorrection, zeta0_center_eq_cosine]
  have hproduct :
      ((1 / 2 : ℂ) + t * I) * ((1 / 2 : ℂ) + t * I - 1) =
        -((t : ℂ) ^ 2 + 1 / 4) := by
    ring_nf
    rw [I_sq]
    ring
  calc
    (1 / 2 : ℂ) +
        (1 / 2 : ℂ) * ((1 / 2 : ℂ) + t * I) *
          ((1 / 2 : ℂ) + t * I - 1) *
            (((2 * ∫ u : ℝ in Ioi 0,
              Real.cos (t * u) * thetaTail u : ℝ)) : ℂ) =
        1 / 2 + (1 / 2 : ℂ) *
          (((1 / 2 : ℂ) + t * I) *
            ((1 / 2 : ℂ) + t * I - 1)) *
              (((2 * ∫ u : ℝ in Ioi 0,
                Real.cos (t * u) * thetaTail u : ℝ)) : ℂ) := by ring
    _ = ((1 / 2 - (t ^ 2 + 1 / 4) *
        ∫ u : ℝ in Ioi 0,
          Real.cos (t * u) * thetaTail u : ℝ) : ℂ) := by
      rw [hproduct]
      norm_cast
      push_cast
      ring

end

end XiThetaCosine

end CarrySelfAdjointOperator
