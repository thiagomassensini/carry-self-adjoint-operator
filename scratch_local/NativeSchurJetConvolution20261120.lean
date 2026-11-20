import CarrySelfAdjointOperator.NativeCompletedSourceFourthPositiveChannel
import Mathlib.Tactic

namespace CarrySelfAdjointOperator.SourcePositiveReduction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

private theorem jet_factorial_choose (n i : ℕ) (hi : i ≤ n) :
    (n.choose i : ℂ) / (n.factorial : ℂ) =
      1 / ((i.factorial : ℂ) * ((n - i).factorial : ℂ)) := by
  have hfac : (n.choose i : ℂ) *
        (i.factorial : ℂ) * ((n - i).factorial : ℂ) =
      (n.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have hn : (n.factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hi' : (i.factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hni : ((n-i).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n-i))
  field_simp [hn, hi', hni]
  linear_combination hfac

/-- A reusable exact coefficient convolution for the analytic native jets,
with the factorial normalization fixed by the original source. -/
theorem greenTaylorJet_mul
    (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (n : ℕ) :
    completedGreenTaylorJet (f*g) n =
      ∑ i ∈ Finset.range (n+1),
        completedGreenTaylorJet f i *
          completedGreenTaylorJet g (n-i) := by
  unfold completedGreenTaylorJet
  rw [iteratedDeriv_mul (hf.contDiffAt : ContDiffAt ℂ n f 0)
        (hg.contDiffAt : ContDiffAt ℂ n g 0)]
  simp only [smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hle : i ≤ n := by
    have hlt := Finset.mem_range.mp hi
    omega
  have hfac := jet_factorial_choose n i hle
  simp only [div_eq_mul_inv, one_mul, mul_inv_rev] at hfac
  calc
    _ = ((n.choose i : ℂ) * (n.factorial : ℂ)⁻¹) *
          (iteratedDeriv i f 0 * iteratedDeriv (n-i) g 0) := by ring
    _ = _ := by rw [hfac]; ring



private theorem series_coeff_eq_jet
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt f p 0) (n : ℕ) :
    p.coeff n = completedGreenTaylorJet f n := by
  rcases hp with ⟨radius, hball⟩
  have hd := hball.factorial_smul (1 : ℂ) n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at hd
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    Finset.prod_const_one, one_smul] at hd
  have he : (n.factorial : ℂ) • p.coeff n = iteratedDeriv n f 0 := by
    simpa only [Nat.cast_smul_eq_nsmul] using hd
  rw [completedGreenTaylorJet, ←he, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_smul]

/-- The removable divided difference of z*f(z) is the function f
itself, including its value at the center. -/
theorem dslope_z_mul (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    dslope (fun z : ℂ => z * f z) 0 = f := by
  funext z
  by_cases hz : z = 0
  · subst z
    rw [dslope_same]
    have hder := deriv_fun_mul (c := fun z : ℂ => z) (d := f)
      (differentiableAt_id) hf.differentiableAt
    simpa only [deriv_id'', one_mul, zero_mul, add_zero] using hder
  · rw [dslope_of_ne _ hz]
    simp [slope, hz, vsub_eq_sub]

/-- Exact shift of Taylor jets by multiplication with the coordinate. -/
theorem greenTaylorJet_z_mul
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    completedGreenTaylorJet (fun z : ℂ => z * f z) (n+1) =
      completedGreenTaylorJet f n := by
  let g : ℂ → ℂ := fun z => z * f z
  have hg : AnalyticAt ℂ g 0 := analyticAt_id.mul hf
  have hds : dslope g 0 = f := dslope_z_mul f hf
  rcases hg with ⟨p, hp⟩
  calc
    completedGreenTaylorJet g (n+1) = p.coeff (n+1) :=
      (series_coeff_eq_jet hp (n+1)).symm
    _ = p.fslope.coeff n := (FormalMultilinearSeries.coeff_fslope).symm
    _ = completedGreenTaylorJet (dslope g 0) n :=
      series_coeff_eq_jet hp.has_fpower_series_dslope_fslope n
    _ = completedGreenTaylorJet f n := by rw [hds]
end
end CarrySelfAdjointOperator.SourcePositiveReduction
