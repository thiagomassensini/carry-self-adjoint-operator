import CarrySelfAdjointOperator.NativeGammaC9Analytic

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped MeasureTheory
open Set MeasureTheory NativeCarrySpectralWeyl.Infinite
noncomputable section
set_option autoImplicit false

def nativeC9Density (x : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 3).indicator (fun _ => -96/139) x +
    (Ioc (3 : ℝ) 4).indicator (fun _ => 128/139) x +
    (Ioc (4 : ℝ) 6).indicator (fun _ => 80/139) x

theorem nativeC9Density_literal (x : ℝ) :
    nativeC9Density x = if x ≤ 0 then 0 else if x ≤ 3 then -96/139 else
      if x ≤ 4 then 128/139 else if x ≤ 6 then 80/139 else 0 := by
  unfold nativeC9Density
  split_ifs <;> simp_all only [indicator_apply, mem_Ioc] <;> split_ifs <;>
    aesop (add safe (by linarith))

theorem nativeC9Density_integrable : Integrable nativeC9Density volume := by
  have hi (a b c : ℝ) : Integrable ((Ioc a b).indicator (fun _ => c)) volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))
  exact ((hi 0 3 (-96/139)).add (hi 3 4 (128/139))).add (hi 4 6 (80/139))

theorem nativeC9Density_mass_zero : (∫ x, nativeC9Density x) = 0 := by
  have hi (a b c : ℝ) : Integrable ((Ioc a b).indicator (fun _ => c)) volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))
  change (∫ x, ((Ioc (0 : ℝ) 3).indicator (fun _ => (-96/139 : ℝ)) +
    (Ioc (3 : ℝ) 4).indicator (fun _ => (128/139 : ℝ))) x +
    (Ioc (4 : ℝ) 6).indicator (fun _ => (80/139 : ℝ)) x) = 0
  rw [integral_add ((hi 0 3 (-96/139)).add (hi 3 4 (128/139)))
    (hi 4 6 (80/139))]
  simp only [Pi.add_apply]
  rw [integral_add (hi 0 3 (-96/139)) (hi 3 4 (128/139))]
  simp [integral_indicator, measureReal_def]
  norm_num

theorem nativeC9Beta_real_density (z : ℂ) (hz : z.im ≠ 0) :
    (nativeC9Beta z).re = ∫ x, nativeC9Density x *
      (logarithmicResolventRealCoefficient z x - logarithmicResolventRealCoefficient z 3) := by
  let f : ℝ → ℝ := fun x => logarithmicResolventRealCoefficient z x -
    logarithmicResolventRealCoefficient z 3
  have hi (a b c : ℝ) : Integrable ((Ioc a b).indicator (fun x => c*f x)) volume := by
    apply (integrable_indicator_iff measurableSet_Ioc).mpr
    exact ((nativeCauchyReal_integrableOn z hz a b).sub (integrableOn_const (by simp))).const_mul c
  have he : (fun x => nativeC9Density x * f x) =
      (Ioc (0 : ℝ) 3).indicator (fun x => (-96/139)*f x) +
      (Ioc (3 : ℝ) 4).indicator (fun x => (128/139)*f x) +
      (Ioc (4 : ℝ) 6).indicator (fun x => (80/139)*f x) := by
    funext x
    simp only [nativeC9Density, Pi.add_apply, add_mul, indicator_mul_left]
  change _ = ∫ x, nativeC9Density x * f x
  rw [he]
  change _ = ∫ x, ((Ioc (0 : ℝ) 3).indicator (fun x => (-96/139)*f x) +
    (Ioc (3 : ℝ) 4).indicator (fun x => (128/139)*f x)) x +
    (Ioc (4 : ℝ) 6).indicator (fun x => (80/139)*f x) x
  rw [integral_add ((hi 0 3 (-96/139)).add (hi 3 4 (128/139))) (hi 4 6 (80/139))]
  simp only [Pi.add_apply]
  rw [integral_add (hi 0 3 (-96/139)) (hi 3 4 (128/139)),
    integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc,
    integral_indicator measurableSet_Ioc, integral_const_mul, integral_const_mul, integral_const_mul,
    nativeC9Beta_real_centered z hz]
  have hf : (fun x => logarithmicResolventRealCoefficient z 3 -
      logarithmicResolventRealCoefficient z x) = -f := by funext x; simp [f]
  rw [hf, integral_neg']
  simp only [f]
  ring

theorem nativeC9Density_outside (x : ℝ) (hx : x ∉ Ioc 0 6) : nativeC9Density x = 0 := by
  have he : x ≤ 0 ∨ 6 < x := by simpa only [mem_Ioc, not_and_or, not_lt, not_le] using hx
  rcases he with h0 | h6
  · simp [nativeC9Density_literal, h0]
  · have h0 : ¬x ≤ 0 := by linarith
    have h3 : ¬x ≤ 3 := by linarith
    have h4 : ¬x ≤ 4 := by linarith
    simp [nativeC9Density_literal, h0, h3, h4, not_le.mpr h6]

theorem nativeC9Beta_real_density_interval (z : ℂ) (hz : z.im ≠ 0) :
    (nativeC9Beta z).re = ∫ x in Ioc 0 6, nativeC9Density x *
      (logarithmicResolventRealCoefficient z x - logarithmicResolventRealCoefficient z 3) := by
  rw [nativeC9Beta_real_density z hz, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    by_cases hx : x ∈ Ioc (0 : ℝ) 6
    · simp [hx]
    · simp [hx, nativeC9Density_outside x hx])

end
end CarrySelfAdjointOperator.GammaMaterialSewing
