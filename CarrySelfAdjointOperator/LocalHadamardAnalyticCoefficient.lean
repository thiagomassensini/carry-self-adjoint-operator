import CarrySelfAdjointOperator.LocalHadamardAnalyticDeflation
import Mathlib.Tactic

/-!
# Analytic coefficient bridge at a simple zero

The analytic deflation used in the original local Hadamard jet bridge
has Taylor coefficients exactly equal to the derivatives prescribed
by the completed-native characteristic. No zeros except the known
anchor are supplied, and no positivity or global spectral premise
is used.
-/

namespace CarrySelfAdjointOperator
open scoped BigOperators
noncomputable section

/-- Derivatives of a once-divided Taylor factor. The zero factor
moves the Taylor index up by exactly one, with the factorial
normalization required by local Hadamard moments. -/
private theorem iteratedDeriv_mul_id_at_zero
    (u : ℂ → ℂ) (hu : AnalyticAt ℂ u 0) (n : ℕ) :
    iteratedDeriv (n + 1) (fun z : ℂ => z * u z) 0 =
      (n + 1 : ℂ) * iteratedDeriv n u 0 := by
  have h :=
    iteratedDeriv_fun_mul (n := n + 1) (x := (0 : ℂ))
      (f := fun z : ℂ => z) (g := u)
      (by fun_prop : ContDiffAt ℂ (n + 1) (fun z : ℂ => z) 0)
      hu.contDiffAt
  rw [h]
  simp only [iteratedDeriv_fun_id_zero, mul_ite, ite_mul,
    zero_mul, mul_zero]
  simp

/-- An analytic simple zero has a normalized removable quotient
whose complete Taylor jet comes from the higher derivatives of
the original source, including the index shift and factorial.
This is an analytic (not merely formal-series) statement. -/
theorem analyticSimpleZero_normalizedDeflatedGerm_coefficients
    (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0)
    (hzero : f 0 = 0)
    (hsimple : deriv f 0 ≠ 0) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g 0 ∧
      g 0 = 1 ∧
      (∀ v : ℂ, v ≠ 0 →
        g v = f v / (v * deriv f 0)) ∧
      ∀ n : ℕ,
        iteratedDeriv n g 0 / (n.factorial : ℂ) =
          (iteratedDeriv (n + 1) f 0 /
            ((n + 1).factorial : ℂ)) / deriv f 0 := by
  obtain ⟨u, hu, hTaylor⟩ := hf.exists_eq_sum_add_pow_mul 1
  have hfactor : ∀ v : ℂ, f v = v * u v := by
    intro v
    simpa [hzero] using hTaylor v
  have heq : f = fun v : ℂ => v * u v := by
    funext v
    exact hfactor v
  have hdu :=
    (hasDerivAt_id (0 : ℂ)).mul hu.differentiableAt.hasDerivAt
  have hderiv : deriv f 0 = u 0 := by
    rw [heq]
    change deriv (id * u) 0 = u 0
    simpa using hdu.deriv
  refine ⟨fun v => u v / deriv f 0, hu.div_const, ?_, ?_, ?_⟩
  · rw [hderiv]
    exact div_self (by simpa only [hderiv] using hsimple)
  · intro v hv
    rw [hfactor v]
    field_simp [hv, hsimple]
  · intro n
    have hmul := iteratedDeriv_mul_id_at_zero u hu n
    have hshift : iteratedDeriv (n + 1) f 0 =
        (n + 1 : ℂ) * iteratedDeriv n u 0 := by
      rw [heq]
      exact hmul
    rw [iteratedDeriv_div_const, hshift]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp

/-- Exact identification of the analytic Taylor jet for the completed
native F at a simple real zero, with the original camera/global
normalization retained upstream. -/
theorem completedNative_simpleZero_deflatedGerm_coefficients
    (gamma : ℝ)
    (hdomain : (gamma : ℂ) ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic (gamma : ℂ) = 0)
    (hsimple : deriv completedNativeOperatorCharacteristic (gamma : ℂ) ≠ 0) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g 0 ∧
      g 0 = 1 ∧
      (∀ v : ℂ, v ≠ 0 →
        g v = completedNativeOperatorCharacteristic ((gamma : ℂ) + v) /
          (v * deriv completedNativeOperatorCharacteristic (gamma : ℂ))) ∧
      ∀ n : ℕ,
        iteratedDeriv n g 0 / (n.factorial : ℂ) =
          nativeLocalDeflatedCoefficient gamma n := by
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
  obtain ⟨g, hg, h0, hq, hc⟩ :=
    analyticSimpleZero_normalizedDeflatedGerm_coefficients
      (fun v : ℂ => completedNativeOperatorCharacteristic ((gamma : ℂ) + v))
      hshiftAnalytic hzeroShift hsimpleShift
  refine ⟨g, hg, h0, ?_, ?_⟩
  · intro v hv
    simpa only [hderiv] using hq v hv
  · intro n
    have htrans :
      iteratedDeriv (n + 1)
        (fun v : ℂ =>
          completedNativeOperatorCharacteristic ((gamma : ℂ) + v)) 0 =
        iteratedDeriv (n + 1) completedNativeOperatorCharacteristic (gamma : ℂ) := by
      -- The identity holds globally for a translated height variable.
      have ht := congrArg (fun h : ℂ → ℂ => h (0 : ℂ))
        (iteratedDeriv_comp_add_const
          (n := n + 1)
          (f := completedNativeOperatorCharacteristic)
          (s := (gamma : ℂ)))
      convert ht using 1
      · congr 1
        funext v
        exact congrArg completedNativeOperatorCharacteristic (add_comm (gamma : ℂ) v)
      · simp
    rw [hc, htrans, hderiv]
    simp only [nativeLocalDeflatedCoefficient, iteratedDeriv_one]

/-- The local moments read from *any* supported completed camera are
exactly the local moments of the analytic deflated germ: this combines
the geometric camera/cutoff equivalence with the analytic Taylor
coefficient identification. -/
theorem cameraLocalHadamard_analyticReadout
    {camera : ℕ} (hcamera : 2 ≤ camera)
    (cutoff : ℕ) (gamma : ℝ)
    (hdomain : (gamma : ℂ) ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic (gamma : ℂ) = 0)
    (hsimple : deriv completedNativeOperatorCharacteristic (gamma : ℂ) ≠ 0) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g 0 ∧
      g 0 = 1 ∧
      (∀ v : ℂ, v ≠ 0 →
        g v = completedNativeOperatorCharacteristic ((gamma : ℂ) + v) /
          (v * deriv completedNativeOperatorCharacteristic (gamma : ℂ))) ∧
      (∀ n : ℕ,
        iteratedDeriv n g 0 / (n.factorial : ℂ) =
          cameraLocalDeflatedCoefficient camera cutoff gamma n) ∧
      ∀ m : ℕ,
        localHadamardMoment
            (fun n => iteratedDeriv n g 0 / (n.factorial : ℂ)) m =
          cameraLocalHadamardMoment camera cutoff gamma m := by
  obtain ⟨g, hg, h0, hq, hc⟩ :=
    completedNative_simpleZero_deflatedGerm_coefficients
      gamma hdomain hzero hsimple
  refine ⟨g, hg, h0, hq, ?_, ?_⟩
  · intro n
    rw [cameraLocalDeflatedCoefficient_eq_native hcamera cutoff gamma n]
    exact hc n
  · intro m
    unfold cameraLocalHadamardMoment
    congr 1
    funext n
    rw [cameraLocalDeflatedCoefficient_eq_native hcamera cutoff gamma n]
    exact hc n

end
end CarrySelfAdjointOperator
