import CarrySelfAdjointOperator.LocalHadamardFormalSeriesBridge
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic

/-!
# Analytic removable simple-zero quotient, independent of any zero table

This generic theorem turns a simple zero of an analytic complex function
into a normalized analytic deflated germ. It does not yet identify every
coefficient of that germ with the iterated derivative formula used by the
formal moment recurrence: that coefficient-shift theorem is a separate
analytic seam.
-/

namespace CarrySelfAdjointOperator
noncomputable section

/-- An analytic simple zero has a removable normalized quotient,
with value one at the anchor. This is a source-independent analytic
lemma and is valid without a product over zeros. -/
theorem analyticSimpleZero_normalizedDeflatedGerm
    (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0)
    (hzero : f 0 = 0)
    (hsimple : deriv f 0 ≠ 0) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g 0 ∧
      g 0 = 1 ∧
      ∀ z : ℂ, z ≠ 0 →
        g z = f z / (z * deriv f 0) := by
  obtain ⟨u, hu, hTaylor⟩ := hf.exists_eq_sum_add_pow_mul 1
  have hfactor : ∀ z : ℂ, f z = z * u z := by
    intro z
    simpa [hzero] using hTaylor z
  have hderiv : deriv f 0 = u 0 := by
    have heq : f = fun z : ℂ => z * u z := by
      funext z
      exact hfactor z
    rw [heq]
    have hdu :=
      (hasDerivAt_id (0 : ℂ)).mul hu.differentiableAt.hasDerivAt
    change deriv (id * u) 0 = u 0
    simpa using hdu.deriv
  refine ⟨fun z => u z / deriv f 0, hu.div_const, ?_, ?_⟩
  · rw [hderiv]
    exact div_self (by simpa only [hderiv] using hsimple)
  · intro z hz
    rw [hfactor z]
    field_simp [hz, hsimple]

/-- Specialization to the completed native characteristic, retaining
the source domain, zero, and simplicity as explicit hypotheses.
No zero table, RH, or global spectral positivity is used. -/
theorem completedNative_simpleZero_normalizedDeflatedGerm
    (gamma : ℝ)
    (hdomain : (gamma : ℂ) ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic (gamma : ℂ) = 0)
    (hsimple : deriv completedNativeOperatorCharacteristic (gamma : ℂ) ≠ 0) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g 0 ∧
      g 0 = 1 ∧
      ∀ v : ℂ, v ≠ 0 →
        g v = completedNativeOperatorCharacteristic ((gamma : ℂ) + v) /
          (v * deriv completedNativeOperatorCharacteristic (gamma : ℂ)) := by
  have hF := completedNativeOperatorCharacteristic_analyticAt hdomain
  have hshift : HasDerivAt (fun v : ℂ => (gamma : ℂ) + v) 1 0 :=
    (hasDerivAt_id (0 : ℂ)).const_add (gamma : ℂ)
  have hshiftAnalytic :
      AnalyticAt ℂ (fun v : ℂ =>
        completedNativeOperatorCharacteristic ((gamma : ℂ) + v)) 0 := by
    have hsa : AnalyticAt ℂ (fun v : ℂ => (gamma : ℂ) + v) 0 := by fun_prop
    have hF0 : AnalyticAt ℂ completedNativeOperatorCharacteristic
        ((gamma : ℂ) + 0) := by simpa using hF
    simpa [Function.comp_def] using
      (AnalyticAt.comp
        (f := fun v : ℂ => (gamma : ℂ) + v) hF0 hsa)
  have hderiv :
      deriv (fun v : ℂ =>
        completedNativeOperatorCharacteristic ((gamma : ℂ) + v)) 0 =
        deriv completedNativeOperatorCharacteristic (gamma : ℂ) := by
    have hFderiv : HasDerivAt completedNativeOperatorCharacteristic
        (deriv completedNativeOperatorCharacteristic (gamma : ℂ))
        ((gamma : ℂ) + 0) := by
      simpa using hF.differentiableAt.hasDerivAt
    have hcomp := HasDerivAt.comp
      (h := fun v : ℂ => (gamma : ℂ) + v)
      0 hFderiv hshift
    change deriv
      (completedNativeOperatorCharacteristic ∘
        (fun v : ℂ => (gamma : ℂ) + v)) 0 = _
    simpa using hcomp.deriv
  have hzeroShift :
      (fun v : ℂ => completedNativeOperatorCharacteristic ((gamma : ℂ) + v)) 0 = 0 := by
    simpa using hzero
  have hsimpleShift :
      deriv (fun v : ℂ =>
        completedNativeOperatorCharacteristic ((gamma : ℂ) + v)) 0 ≠ 0 := by
    rw [hderiv]
    exact hsimple
  obtain ⟨g, hg, h0, hq⟩ :=
    analyticSimpleZero_normalizedDeflatedGerm
      (fun v : ℂ => completedNativeOperatorCharacteristic ((gamma : ℂ) + v))
      hshiftAnalytic hzeroShift hsimpleShift
  refine ⟨g, hg, h0, ?_⟩
  intro v hv
  simpa only [hderiv] using hq v hv

end
end CarrySelfAdjointOperator
