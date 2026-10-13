import CarrySelfAdjointOperator.CompletedNativeLocalProductGreenAudit
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RealDeriv

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped ComplexConjugate
open Filter Set
noncomputable section
set_option autoImplicit false

theorem realGamma_quarter_deriv_nonpos : deriv Real.Gamma (1/4 : ℝ) ≤ 0 := by
  have h := Real.Gamma_strictAntiOn_Ioc.antitoneOn.derivWithin_nonpos
    (x := (1/4 : ℝ))
  have hn : Set.Ioc (0 : ℝ) 1 ∈ nhds (1/4 : ℝ) := by
    exact mem_of_superset (Ioo_mem_nhds (by norm_num) (by norm_num)) Set.Ioo_subset_Ioc_self
  rwa [derivWithin_of_mem_nhds hn] at h

theorem complexGamma_quarter_hasDerivAt :
    HasDerivAt Complex.Gamma (deriv Complex.Gamma (1/4 : ℂ)) (1/4 : ℂ) := by
  apply (Complex.differentiableAt_Gamma _ ?_).hasDerivAt
  intro m hm
  have hr := congrArg Complex.re hm
  have hmpos : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  norm_num at hr
  linarith

theorem complexGamma_quarter_deriv_re :
    (deriv Complex.Gamma (1/4 : ℂ)).re = deriv Real.Gamma (1/4 : ℝ) := by
  have hc : HasDerivAt Complex.Gamma (deriv Complex.Gamma (1/4 : ℂ))
      ((1/4 : ℝ) : ℂ) := by
    rw [show ((1/4 : ℝ) : ℂ) = (1/4 : ℂ) by norm_num]
    exact complexGamma_quarter_hasDerivAt
  have h := hc.real_of_complex
  simpa only [Complex.Gamma_ofReal, Complex.ofReal_re] using h.deriv.symm

theorem nativeXiCompletionFactor_deriv_zero_formula :
    deriv nativeXiCompletionFactor 0 =
      -(Complex.I / 16) * (Real.exp (-Real.log Real.pi / 4) : ℂ) *
        (deriv Complex.Gamma (1/4 : ℂ) -
          (Real.log Real.pi : ℂ) * Complex.Gamma (1/4 : ℂ)) := by
  have hs := hasDerivAt_operatorHeightParameter 0
  have hp : HasDerivAt (fun z : ℂ =>
      (1/2 : ℂ) * operatorHeightParameter z * (operatorHeightParameter z - 1)) 0 0 := by
    have h := (hs.const_mul (1/2 : ℂ)).mul (hs.sub_const 1)
    have hz : (1/2 : ℂ) * Complex.I * (operatorHeightParameter 0 - 1) +
        (1/2 : ℂ) * operatorHeightParameter 0 * Complex.I = 0 := by
      norm_num [operatorHeightParameter]
      ring
    rw [hz] at h
    exact h
  have he := (((hs.div_const 2).neg).mul_const (Real.log Real.pi : ℂ)).cexp
  have hg : HasDerivAt (fun z : ℂ => Complex.Gamma (operatorHeightParameter z / 2))
      (deriv Complex.Gamma (1/4 : ℂ) * (Complex.I / 2)) 0 := by
    have hbase : HasDerivAt Complex.Gamma (deriv Complex.Gamma (1/4 : ℂ))
        (operatorHeightParameter 0 / 2) := by
      rw [show operatorHeightParameter 0 / 2 = (1/4 : ℂ) by norm_num [operatorHeightParameter]]
      exact complexGamma_quarter_hasDerivAt
    exact hbase.comp 0 (hs.div_const 2)
  have hexp : Complex.exp (-(operatorHeightParameter 0 / 2) * (Real.log Real.pi : ℂ)) =
      (Real.exp (-Real.log Real.pi / 4) : ℂ) := by
    rw [show -(operatorHeightParameter 0 / 2) * (Real.log Real.pi : ℂ) =
      ((-Real.log Real.pi / 4 : ℝ) : ℂ) by
        push_cast
        norm_num [operatorHeightParameter]
        ring]
    exact (Complex.ofReal_exp _).symm
  have hd := ((hp.mul he).mul hg).deriv
  change deriv nativeXiCompletionFactor 0 = _ at hd
  dsimp only [Pi.mul_apply, Pi.neg_apply] at hd
  rw [hd, hexp]
  norm_num [operatorHeightParameter]
  ring

theorem nativeXiCompletionFactor_deriv_zero_im_formula :
    (deriv nativeXiCompletionFactor 0).im =
      Real.exp (-Real.log Real.pi / 4) / 16 *
        (Real.log Real.pi * Real.Gamma (1/4 : ℝ) - deriv Real.Gamma (1/4 : ℝ)) := by
  rw [nativeXiCompletionFactor_deriv_zero_formula]
  have hg : Complex.Gamma (1/4 : ℂ) = (Real.Gamma (1/4 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      Complex.Gamma_ofReal (1/4 : ℝ)
  have halgebra (e l g : ℝ) (d : ℂ) :
      (-(Complex.I / 16) * (e : ℂ) * (d - (l : ℂ) * (g : ℂ))).im =
        e / 16 * (l * g - d.re) := by
    norm_num [Complex.mul_im, Complex.mul_re]
    ring
  rw [hg, halgebra, complexGamma_quarter_deriv_re]

theorem nativeXiCompletionFactor_deriv_zero_im_pos :
    0 < (deriv nativeXiCompletionFactor 0).im := by
  rw [nativeXiCompletionFactor_deriv_zero_im_formula]
  have hlog : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.two_le_pi])
  have hgamma : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  exact mul_pos (div_pos (Real.exp_pos _) (by norm_num))
    (sub_pos.mpr (lt_of_le_of_lt realGamma_quarter_deriv_nonpos (mul_pos hlog hgamma)))

theorem nativeXiCompletionFactor_deriv_zero_ne_zero : deriv nativeXiCompletionFactor 0 ≠ 0 := by
  intro h
  have hi := nativeXiCompletionFactor_deriv_zero_im_pos
  rw [h, Complex.zero_im] at hi
  exact (lt_irrefl 0) hi

theorem nativeHeightScalar_deriv_zero_ne_zero : deriv nativeHeightScalar 0 ≠ 0 := by
  intro h
  have hc := nativeCompletionFactor_nativeHeightScalar_firstDerivative_cancel
  rw [h, mul_zero, add_zero] at hc
  exact (mul_ne_zero nativeXiCompletionFactor_deriv_zero_ne_zero nativeHeightScalar_zero_ne_zero) hc

theorem nativeHeightScalar_centerWronskian_eq :
    completedGreenWronskian nativeHeightScalar nativeHeightScalarBoundaryCompanion 0 0 =
      -2 * nativeHeightScalar 0 * deriv nativeHeightScalar 0 := by
  unfold completedGreenWronskian nativeHeightScalarBoundaryCompanion
  rw [nativeHeightScalar_zero_conj, map_neg, nativeHeightScalar_deriv_zero_conj]
  ring

theorem nativeHeightScalar_centerWronskian_ne_zero :
    completedGreenWronskian nativeHeightScalar nativeHeightScalarBoundaryCompanion 0 0 ≠ 0 := by
  rw [nativeHeightScalar_centerWronskian_eq]
  exact mul_ne_zero (mul_ne_zero (by norm_num) nativeHeightScalar_zero_ne_zero)
    nativeHeightScalar_deriv_zero_ne_zero

theorem not_nativeC3GreenRepresentationOn :
    ¬ HasDivisionFreeGreenRepresentationOn completedNativeHeightDomain
      nativeHeightScalar nativeHeightScalarBoundaryCompanion canonicalCompletedOperatorC3HilbertState :=
  not_nativeC3GreenRepresentationOn_of_deriv_ne_zero nativeHeightScalar_deriv_zero_ne_zero

end
end CarrySelfAdjointOperator.GammaMaterialSewing
