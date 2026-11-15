import CarrySelfAdjointOperator.CompletedNativeHardyAnalytic
import CarrySelfAdjointOperator.NativeScalarZetaIdentification
import CarrySelfAdjointOperator.CompletedOperatorCharacteristic
import CPFormal.Analytic.CpGenuineQuotient
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Tactic

/-!
# Entire classical comparison for the native completed characteristic

This file begins the comparison with the entire completion `completedRiemannZeta₀`.
The comparison is downstream of the original native construction and is used only
to study the same canonical moment sequence.
-/

namespace CarrySelfAdjointOperator
open Complex
open scoped ComplexOrder
open Filter Topology
open Asymptotics
open CPFormal.Analytic.Cp
open LSeries

noncomputable section

/-- Entire completed comparison function in the spectral variable. -/
def completedNativeHarmonicComparison (s : ℂ) : ℂ :=
  (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- The same entire comparison, expressed in the centered height variable. -/
def completedNativeHarmonicComparisonAtHeight (z : ℂ) : ℂ :=
  completedNativeHarmonicComparison (operatorHeightParameter z)

theorem differentiable_completedNativeHarmonicComparison :
    Differentiable ℂ completedNativeHarmonicComparison := by
  have hpoly : Differentiable ℂ (fun s : ℂ => s * (s - 1)) := by fun_prop
  have hprod := hpoly.mul differentiable_completedZeta₀
  have hconst : Differentiable ℂ (fun _ : ℂ => (1 : ℂ)) := differentiable_const 1
  have hsum := hprod.add hconst
  change Differentiable ℂ (fun s : ℂ =>
    (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2)
  exact hsum.div_const (2 : ℂ)

theorem differentiable_completedNativeHarmonicComparisonAtHeight :
    Differentiable ℂ completedNativeHarmonicComparisonAtHeight := by
  have hlin : Differentiable ℂ operatorHeightParameter := by
    unfold operatorHeightParameter
    fun_prop
  exact differentiable_completedNativeHarmonicComparison.comp hlin

/-- On the open strip, the entire comparison agrees with the usual completed
zeta expression. -/
theorem completedNativeHarmonicComparison_eq_gammaR_mul_zeta
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsRe : 0 < s.re) :
    completedNativeHarmonicComparison s =
      (s * (s - 1) / 2) * Gammaℝ s * riemannZeta s := by
  have hGamma : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hsRe
  have hZeta := riemannZeta_eq_completedRiemannZeta₀ hs0
  have hZeta' : riemannZeta s =
      (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) / Complex.Gammaℝ s := by
    simpa [Complex.Gammaℝ_def] using hZeta
  have hmul : Complex.Gammaℝ s * riemannZeta s =
      completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) := by
    rw [hZeta']
    field_simp [hGamma]
  unfold completedNativeHarmonicComparison
  have hs1' : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hs0' : s ≠ 0 := hs0
  calc
    (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2 =
        (s * (s - 1) / 2) *
          (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) := by
            field_simp [hs0', hs1']
            ring
    _ = (s * (s - 1) / 2) * (Complex.Gammaℝ s * riemannZeta s) := by rw [hmul]
    _ = (s * (s - 1) / 2) * Complex.Gammaℝ s * riemannZeta s := by ring

/-- In the open native height strip, the entire comparison is the original
completed native characteristic. -/
theorem completedNativeHarmonicComparisonAtHeight_eq_nativeCharacteristic
    {z : ℂ} (hz : z ∈ completedNativeHeightDomain) :
    completedNativeHarmonicComparisonAtHeight z =
      completedNativeOperatorCharacteristic z := by
  let s := operatorHeightParameter z
  have hs : s ∈ genuineCriticalStrip := by
    simpa [s, completedNativeHeightDomain] using hz
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num [genuineCriticalStrip] at hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num [genuineCriticalStrip] at hs
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hexp : (Real.pi : ℂ) ^ (-s / 2) =
      Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hpi, ← Complex.ofReal_log Real.pi_pos.le]
    congr 1
    ring
  have hfactor : nativeXiCompletionFactor z =
      (s * (s - 1) / 2) * Complex.Gammaℝ s := by
    change (1 / 2 : ℂ) * s * (s - 1) *
      Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ)) * Complex.Gamma (s / 2) = _
    rw [Complex.Gammaℝ_def, ← hexp]
    ring
  have hstrip := completedNativeOperatorCharacteristic_eq_completedRiemannZeta hs
  have hstrip' : completedNativeOperatorCharacteristic z =
      nativeXiCompletionFactor z * riemannZeta s := by
    simpa [s] using hstrip
  change completedNativeHarmonicComparison s =
    completedNativeOperatorCharacteristic z
  calc
    completedNativeHarmonicComparison s =
        (s * (s - 1) / 2) * Complex.Gammaℝ s * riemannZeta s :=
      completedNativeHarmonicComparison_eq_gammaR_mul_zeta hs0 hs1 hs.1
    _ = nativeXiCompletionFactor z * riemannZeta s := by rw [← hfactor]
    _ = completedNativeOperatorCharacteristic z := hstrip'.symm

/-- The native characteristic and the entire comparison have the same germ
at the centered height. -/
theorem completedNativeHarmonicComparisonAtHeight_eventuallyEq_nativeCharacteristic :
    (fun z => completedNativeHarmonicComparisonAtHeight z) =ᶠ[𝓝 0]
      completedNativeOperatorCharacteristic := by
  filter_upwards [isOpen_completedNativeHeightDomain.mem_nhds
    zero_mem_completedNativeHeightDomain] with z hz
  exact completedNativeHarmonicComparisonAtHeight_eq_nativeCharacteristic hz

/-- Differential residual obtained from a finite relation, now formed with
the entire comparison function. -/
def completedNativeEntireHardyResidual (D A : Polynomial ℂ) (z : ℂ) : ℂ :=
  D.eval (z ^ 2) * deriv completedNativeHarmonicComparisonAtHeight z +
    (2 : ℂ) * z * A.eval (z ^ 2) * completedNativeHarmonicComparisonAtHeight z

private theorem completedNativeEntireHardyResidual_analyticAt
    (D A : Polynomial ℂ) (z : ℂ) :
    AnalyticAt ℂ (completedNativeEntireHardyResidual D A) z := by
  have hDfun : (fun w : ℂ => D.eval (w ^ 2)) =
      (fun w => ∑ i ∈ Finset.range (D.natDegree + 1),
        D.coeff i * w ^ (2 * i)) := by
    funext w
    rw [Polynomial.eval_eq_sum_range]
    simp only [pow_mul]
  have hAfun : (fun w : ℂ => A.eval (w ^ 2)) =
      (fun w => ∑ i ∈ Finset.range (A.natDegree + 1),
        A.coeff i * w ^ (2 * i)) := by
    funext w
    rw [Polynomial.eval_eq_sum_range]
    simp only [pow_mul]
  have hD : AnalyticAt ℂ (fun w : ℂ => D.eval (w ^ 2)) z := by
    rw [hDfun]
    fun_prop
  have hA : AnalyticAt ℂ (fun w : ℂ => A.eval (w ^ 2)) z := by
    rw [hAfun]
    fun_prop
  have hF := differentiable_completedNativeHarmonicComparisonAtHeight.analyticAt z
  have hF' := hF.deriv
  have hlin : AnalyticAt ℂ (fun w : ℂ => (2 : ℂ) * w) z := by fun_prop
  change AnalyticAt ℂ
    (fun w => D.eval (w ^ 2) * deriv completedNativeHarmonicComparisonAtHeight w +
      (2 : ℂ) * w * A.eval (w ^ 2) * completedNativeHarmonicComparisonAtHeight w) z
  exact (hD.mul hF').add ((hlin.mul hA).mul hF)

theorem completedNativeEntireHardyResidual_eq_zero_of_local_residual
    (D A : Polynomial ℂ)
    (hlocal : (fun z : ℂ => D.eval (z ^ 2) *
      deriv completedNativeOperatorCharacteristic z +
      (2 : ℂ) * z * A.eval (z ^ 2) *
        completedNativeOperatorCharacteristic z) =ᶠ[𝓝 0] fun _ => 0) :
    ∀ z : ℂ, completedNativeEntireHardyResidual D A z = 0 := by
  have hlocalEntire : completedNativeEntireHardyResidual D A =ᶠ[𝓝 0] fun _ => 0 := by
    have hcmp := completedNativeHarmonicComparisonAtHeight_eventuallyEq_nativeCharacteristic
    have hcmpDeriv := hcmp.deriv
    filter_upwards [hlocal, hcmp, hcmpDeriv] with z hz hcmpz hcmpdz
    change D.eval (z ^ 2) * deriv completedNativeOperatorCharacteristic z +
      (2 : ℂ) * z * A.eval (z ^ 2) * completedNativeOperatorCharacteristic z = 0 at hz
    change completedNativeHarmonicComparisonAtHeight z =
      completedNativeOperatorCharacteristic z at hcmpz
    change deriv completedNativeHarmonicComparisonAtHeight z =
      deriv completedNativeOperatorCharacteristic z at hcmpdz
    simp only [completedNativeEntireHardyResidual, hcmpz, hcmpdz]
    exact hz
  have hanalytic : AnalyticOnNhd ℂ (completedNativeEntireHardyResidual D A) Set.univ := by
    intro z hz
    exact completedNativeEntireHardyResidual_analyticAt D A z
  have hzero := hanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (by simp) hlocalEntire
  exact fun z => hzero (Set.mem_univ z)

/-- A finite relation forces the entire comparison residual to vanish on all
of C, by analytic continuation from its original native germ. -/
theorem exists_completedNativeEntireResidual_eq_zero_of_moment_relation
    (s : Finset ℕ) (a : ℕ → ℝ)
    (haNonzero : ∃ i, i ∈ s ∧ a i ≠ 0)
    (hrel : ∀ j : ℕ,
      ∑ i ∈ s, a i * canonicalCompletedNativeLogDerivativeMoment (i + j) = 0) :
    ∃ D A : Polynomial ℂ, D ≠ 0 ∧
      ∀ z : ℂ, completedNativeEntireHardyResidual D A z = 0 := by
  obtain ⟨D, A, hD, hlocal⟩ :=
    exists_completedNativeHardyResidual_of_moment_relation s a haNonzero hrel
  exact ⟨D, A, hD,
    completedNativeEntireHardyResidual_eq_zero_of_local_residual D A hlocal⟩

theorem exists_completedNativeEntireResidual_real_coefficients_eq_zero_of_moment_relation
    (s : Finset ℕ) (a : ℕ → ℝ)
    (haNonzero : ∃ i, i ∈ s ∧ a i ≠ 0)
    (hrel : ∀ j : ℕ,
      ∑ i ∈ s, a i * canonicalCompletedNativeLogDerivativeMoment (i + j) = 0) :
    ∃ D A : Polynomial ℝ, D ≠ 0 ∧
      ∀ z : ℂ, completedNativeEntireHardyResidual
        (Polynomial.map (algebraMap ℝ ℂ) D)
        (Polynomial.map (algebraMap ℝ ℂ) A) z = 0 := by
  obtain ⟨D, A, hD, hlocal⟩ :=
    exists_completedNativeHardyResidual_real_coefficients_of_moment_relation
      s a haNonzero hrel
  exact ⟨D, A, hD,
    completedNativeEntireHardyResidual_eq_zero_of_local_residual
      (Polynomial.map (algebraMap ℝ ℂ) D)
      (Polynomial.map (algebraMap ℝ ℂ) A) hlocal⟩

/-- Polynomial substitution corresponding to the real spectral parameter
`s = 1/2 + i z` at the points `z = -i (s - 1/2)`. -/
def completedNativeHardyIntegerSubstitution : Polynomial ℂ :=
  -(Polynomial.X - Polynomial.C (1 / 2 : ℂ)) ^ 2

def completedNativeHardyIntegerDenominator (D : Polynomial ℂ) : Polynomial ℂ :=
  D.comp completedNativeHardyIntegerSubstitution

def completedNativeHardyIntegerNumerator (A : Polynomial ℂ) : Polynomial ℂ :=
  (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
    A.comp completedNativeHardyIntegerSubstitution

def completedNativeHardyIntegerSubstitutionReal : Polynomial ℝ :=
  -(Polynomial.X - Polynomial.C (1 / 2 : ℝ)) ^ 2

def completedNativeHardyIntegerDenominatorReal (D : Polynomial ℝ) : Polynomial ℝ :=
  D.comp completedNativeHardyIntegerSubstitutionReal

def completedNativeHardyIntegerNumeratorReal (A : Polynomial ℝ) : Polynomial ℝ :=
  (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
    A.comp completedNativeHardyIntegerSubstitutionReal

private theorem completedNativeHardyIntegerSubstitution_eq_mapReal :
    Polynomial.map (algebraMap ℝ ℂ) completedNativeHardyIntegerSubstitutionReal =
      completedNativeHardyIntegerSubstitution := by
  simp [completedNativeHardyIntegerSubstitution,
    completedNativeHardyIntegerSubstitutionReal]

theorem completedNativeHardyIntegerDenominator_eq_map (D : Polynomial ℝ) :
    completedNativeHardyIntegerDenominator (Polynomial.map (algebraMap ℝ ℂ) D) =
      Polynomial.map (algebraMap ℝ ℂ) (completedNativeHardyIntegerDenominatorReal D) := by
  change (Polynomial.map (algebraMap ℝ ℂ) D).comp
      completedNativeHardyIntegerSubstitution =
    Polynomial.map (algebraMap ℝ ℂ)
      (D.comp completedNativeHardyIntegerSubstitutionReal)
  rw [Polynomial.map_comp]
  rw [completedNativeHardyIntegerSubstitution_eq_mapReal]

theorem completedNativeHardyIntegerNumerator_eq_map (A : Polynomial ℝ) :
    completedNativeHardyIntegerNumerator (Polynomial.map (algebraMap ℝ ℂ) A) =
      Polynomial.map (algebraMap ℝ ℂ) (completedNativeHardyIntegerNumeratorReal A) := by
  change (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
      (Polynomial.map (algebraMap ℝ ℂ) A).comp
        completedNativeHardyIntegerSubstitution =
    Polynomial.map (algebraMap ℝ ℂ)
      ((Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
        A.comp completedNativeHardyIntegerSubstitutionReal)
  rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_comp]
  rw [completedNativeHardyIntegerSubstitution_eq_mapReal]
  norm_num

theorem polynomial_map_eval_ofReal (P : Polynomial ℝ) (t : ℝ) :
    (Polynomial.map (algebraMap ℝ ℂ) P).eval (t : ℂ) =
      ((P.eval t : ℝ) : ℂ) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) t

theorem polynomial_map_eval_nat (P : Polynomial ℝ) (m : ℕ) :
    (Polynomial.map (algebraMap ℝ ℂ) P).eval (m : ℂ) =
      ((P.eval (m : ℝ) : ℝ) : ℂ) := by
  simpa using polynomial_map_eval_ofReal P (m : ℝ)

theorem completedNativeHardyIntegerDenominator_ne_zero
    {D : Polynomial ℂ} (hD : D ≠ 0) :
    completedNativeHardyIntegerDenominator D ≠ 0 := by
  let q := completedNativeHardyIntegerSubstitution
  have hqdeg : q.natDegree = 2 := by
    simp [q, completedNativeHardyIntegerSubstitution]
  have hqLC : q.leadingCoeff = -1 := by
    simp [q, completedNativeHardyIntegerSubstitution]
  have hDLC : D.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hD
  have hcompdeg : (D.comp q).natDegree = D.natDegree * 2 := by
    rw [Polynomial.natDegree_comp_eq_of_mul_ne_zero]
    · rw [hqdeg]
    · rw [hqLC]
      exact mul_ne_zero hDLC (pow_ne_zero _ (by norm_num))
  intro hzero
  by_cases hd : D.natDegree = 0
  · have hconst : D = Polynomial.C (D.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero hd
    have hcoeff : D.coeff 0 = 0 := by
      have hzero' : D.comp completedNativeHardyIntegerSubstitution = 0 := by
        simpa [completedNativeHardyIntegerDenominator] using hzero
      rw [hconst] at hzero'
      have hC : Polynomial.C (D.coeff 0) = 0 := by
        simpa [completedNativeHardyIntegerSubstitution] using hzero'
      exact Polynomial.C_eq_zero.mp hC
    exact hD (by rw [hconst, hcoeff]; simp)
  · have hdegzero : D.natDegree * 2 = 0 := by
      rw [completedNativeHardyIntegerDenominator] at hzero
      rw [hzero] at hcompdeg
      simpa using hcompdeg
    omega

theorem completedNativeHardyIntegerDenominator_eval (D : Polynomial ℂ) (t : ℂ) :
    (completedNativeHardyIntegerDenominator D).eval t =
      D.eval (-(t - (1 / 2 : ℂ)) ^ 2) := by
  simp [completedNativeHardyIntegerDenominator,
    completedNativeHardyIntegerSubstitution]

theorem completedNativeHardyIntegerNumerator_eval (A : Polynomial ℂ) (t : ℂ) :
    (completedNativeHardyIntegerNumerator A).eval t =
      (2 * t - 1) * A.eval (-(t - (1 / 2 : ℂ)) ^ 2) := by
  simp [completedNativeHardyIntegerNumerator,
    completedNativeHardyIntegerSubstitution]

/-- The entire differential identity transported to the original real
spectral axis. -/
theorem completedNativeEntireResidual_realAxis
    (D A : Polynomial ℂ) (hidentity : ∀ z,
      completedNativeEntireHardyResidual D A z = 0) (t : ℝ) :
    (completedNativeHardyIntegerDenominator D).eval (t : ℂ) *
        deriv completedNativeHarmonicComparison (t : ℂ) =
      (completedNativeHardyIntegerNumerator A).eval (t : ℂ) *
        completedNativeHarmonicComparison (t : ℂ) := by
  let z : ℂ := -Complex.I * ((t : ℂ) - 1 / 2)
  have hzparam : operatorHeightParameter z = (t : ℂ) := by
    calc
      operatorHeightParameter z = 1 / 2 + Complex.I *
          (-Complex.I * ((t : ℂ) - 1 / 2)) := by rfl
      _ = 1 / 2 + ((t : ℂ) - 1 / 2) := by
        have hI : Complex.I * (-Complex.I) = 1 := by
          calc
            Complex.I * (-Complex.I) = -(Complex.I * Complex.I) := by ring
            _ = 1 := by rw [Complex.I_mul_I]; norm_num
        calc
          1 / 2 + Complex.I * (-Complex.I * ((t : ℂ) - 1 / 2)) =
              1 / 2 + (Complex.I * (-Complex.I)) * ((t : ℂ) - 1 / 2) := by ring
          _ = 1 / 2 + ((t : ℂ) - 1 / 2) := by rw [hI, one_mul]
      _ = (t : ℂ) := by ring
  have hzderiv : deriv completedNativeHarmonicComparisonAtHeight z =
      Complex.I * deriv completedNativeHarmonicComparison (t : ℂ) := by
    have hlin : HasDerivAt operatorHeightParameter Complex.I z := by
      have hsum := (hasDerivAt_const z (1 / 2 : ℂ)).add
        ((hasDerivAt_id z).const_mul Complex.I)
      have heq : (fun w : ℂ => 1 / 2 + Complex.I * w) =ᶠ[nhds z]
          ((fun _ : ℂ => (1 / 2 : ℂ)) + fun w : ℂ => Complex.I * w) := by
        filter_upwards [] with w
        rfl
      have h := hsum.congr_of_eventuallyEq heq
      change HasDerivAt (fun w : ℂ => 1 / 2 + Complex.I * w) _ z at h
      exact h.congr_deriv (by simp)
    have hcomp := differentiable_completedNativeHarmonicComparison.differentiableAt
      |>.hasDerivAt.comp z hlin
    change deriv (completedNativeHarmonicComparison ∘ operatorHeightParameter) z = _
    rw [show (completedNativeHarmonicComparison ∘ operatorHeightParameter) =
      completedNativeHarmonicComparisonAtHeight by rfl] at hcomp
    rw [hzparam] at hcomp
    calc
      deriv completedNativeHarmonicComparisonAtHeight z =
          deriv completedNativeHarmonicComparison (t : ℂ) * Complex.I := hcomp.deriv
      _ = Complex.I * deriv completedNativeHarmonicComparison (t : ℂ) := by ring
  have hz2 : z ^ 2 = -((t : ℂ) - 1 / 2) ^ 2 := by
    calc
      z ^ 2 = (-Complex.I) ^ 2 * ((t : ℂ) - 1 / 2) ^ 2 := by
        simp only [z]
        ring
      _ = -((t : ℂ) - 1 / 2) ^ 2 := by
        rw [show (-Complex.I : ℂ) ^ 2 = -1 by
          rw [neg_sq, Complex.I_sq]]
        ring
  have hzmul : (2 : ℂ) * z = -(2 * (t : ℂ) - 1) * Complex.I := by
    dsimp [z]
    ring
  have hE := hidentity z
  change D.eval (z ^ 2) * deriv completedNativeHarmonicComparisonAtHeight z +
      (2 : ℂ) * z * A.eval (z ^ 2) *
        completedNativeHarmonicComparisonAtHeight z = 0 at hE
  have hgoal : D.eval (-((t : ℂ) - 1 / 2) ^ 2) *
      deriv completedNativeHarmonicComparison (t : ℂ) =
      (2 * (t : ℂ) - 1) * A.eval (-((t : ℂ) - 1 / 2) ^ 2) *
        completedNativeHarmonicComparison (t : ℂ) := by
    rw [hzderiv, hz2, hzmul] at hE
    simp only [completedNativeHarmonicComparisonAtHeight, hzparam] at hE
    have hE' : Complex.I * ((D.eval (-((t : ℂ) - 1 / 2) ^ 2) *
        deriv completedNativeHarmonicComparison (t : ℂ)) -
        ((2 * (t : ℂ) - 1) * A.eval (-((t : ℂ) - 1 / 2) ^ 2) *
          completedNativeHarmonicComparison (t : ℂ))) = 0 := by
      linear_combination hE
    have hi : Complex.I ≠ 0 := Complex.I_ne_zero
    have hval := (mul_eq_zero.mp hE').resolve_left hi
    exact sub_eq_zero.mp hval
  rw [completedNativeHardyIntegerDenominator_eval,
    completedNativeHardyIntegerNumerator_eval]
  exact hgoal

theorem completedNativeEntireResidual_realAxis_real
    (D A : Polynomial ℝ)
    (hidentity : ∀ z, completedNativeEntireHardyResidual
      (Polynomial.map (algebraMap ℝ ℂ) D)
      (Polynomial.map (algebraMap ℝ ℂ) A) z = 0)
    (t : ℝ) :
    (completedNativeHardyIntegerDenominatorReal D).eval t *
        deriv completedNativeHarmonicComparison (t : ℂ) =
      (completedNativeHardyIntegerNumeratorReal A).eval t *
        completedNativeHarmonicComparison (t : ℂ) := by
  have h := completedNativeEntireResidual_realAxis
    (Polynomial.map (algebraMap ℝ ℂ) D)
    (Polynomial.map (algebraMap ℝ ℂ) A) hidentity t
  rw [completedNativeHardyIntegerDenominator_eq_map,
    completedNativeHardyIntegerNumerator_eq_map,
    polynomial_map_eval_ofReal, polynomial_map_eval_ofReal] at h
  exact h

theorem exists_completedNativeHardyIntegerIdentity_of_moment_relation
    (s : Finset ℕ) (a : ℕ → ℝ)
    (haNonzero : ∃ i, i ∈ s ∧ a i ≠ 0)
    (hrel : ∀ j : ℕ,
      ∑ i ∈ s, a i * canonicalCompletedNativeLogDerivativeMoment (i + j) = 0) :
    ∃ D A : Polynomial ℂ, D ≠ 0 ∧
      ∀ t : ℝ,
        (completedNativeHardyIntegerDenominator D).eval (t : ℂ) *
            deriv completedNativeHarmonicComparison (t : ℂ) =
          (completedNativeHardyIntegerNumerator A).eval (t : ℂ) *
            completedNativeHarmonicComparison (t : ℂ) := by
  obtain ⟨D, A, hD, hzero⟩ :=
    exists_completedNativeEntireResidual_eq_zero_of_moment_relation
      s a haNonzero hrel
  exact ⟨D, A, hD, fun t =>
    completedNativeEntireResidual_realAxis D A hzero t⟩

theorem completedNativeHardyIntegerDenominator_eventually_ne_zero
    {D : Polynomial ℂ} (hD : D ≠ 0) :
    ∀ᶠ n : ℕ in atTop,
      (completedNativeHardyIntegerDenominator D).eval
        ((2 * (n + 1) : ℕ) : ℂ) ≠ 0 := by
  let Q := completedNativeHardyIntegerDenominator D
  have hQ : Q ≠ 0 := by
    exact completedNativeHardyIntegerDenominator_ne_zero hD
  let f : ℕ → ℂ := fun n => ((2 * (n + 1) : ℕ) : ℂ)
  have hf : Function.Injective f := by
    intro m n hmn
    have hcast : 2 * (m + 1) = 2 * (n + 1) := Nat.cast_injective hmn
    omega
  let S : Set ℕ := {n | Q.IsRoot (f n)}
  have hroots : {z : ℂ | Q.IsRoot z}.Finite :=
    Polynomial.finite_setOf_isRoot hQ
  have hS : S.Finite := by
    dsimp [S]
    exact hroots.preimage (Set.injOn_of_injective hf)
  obtain ⟨N, hN⟩ := hS.bddAbove
  have hevent : ∀ᶠ n : ℕ in atTop, n ∉ S := by
    apply Filter.eventually_atTop.2
    refine ⟨N + 1, ?_⟩
    intro n hn hnS
    have hnle : n ≤ N := hN hnS
    omega
  filter_upwards [hevent] with n hn
  change Q.eval (f n) ≠ 0
  intro hroot
  apply hn
  exact hroot

theorem completedNativeHardyIntegerDenominatorReal_eventually_ne_zero
    (D : Polynomial ℝ) (hD : D ≠ 0) :
    ∀ᶠ n : ℕ in atTop,
      (completedNativeHardyIntegerDenominatorReal D).eval
        (2 * ((n + 1 : ℕ) : ℝ)) ≠ 0 := by
  have hmapD : Polynomial.map (algebraMap ℝ ℂ) D ≠ 0 :=
    (Polynomial.map_ne_zero_iff (RingHom.injective (algebraMap ℝ ℂ))).2 hD
  have hevent := completedNativeHardyIntegerDenominator_eventually_ne_zero hmapD
  filter_upwards [hevent] with n hn
  have hn' : (completedNativeHardyIntegerDenominatorReal D).eval
      (2 * ((n + 1 : ℕ) : ℝ) : ℝ) ≠ 0 := by
    intro hzero
    rw [completedNativeHardyIntegerDenominator_eq_map,
      polynomial_map_eval_nat] at hn
    have hz : (completedNativeHardyIntegerDenominatorReal D).eval
        ((2 * (n + 1) : ℕ) : ℝ) = 0 := by
      simpa [Nat.cast_mul, Nat.cast_add] using hzero
    have hzcast : (((completedNativeHardyIntegerDenominatorReal D).eval
        ((2 * (n + 1) : ℕ) : ℝ) : ℝ) : ℂ) = 0 := by exact_mod_cast hz
    rw [hzcast] at hn
    exact hn rfl
  exact hn'

private theorem completedNativeGammaR_logDeriv_at_even_nat (n : ℕ) :
    deriv Complex.Gammaℝ (2 * ((n + 1 : ℕ) : ℂ)) /
        Complex.Gammaℝ (2 * ((n + 1 : ℕ) : ℂ)) =
      -Complex.log (Real.pi : ℂ) / 2 +
        ((-Real.eulerMascheroniConstant + (harmonic n : ℝ) : ℝ) : ℂ) / 2 := by
  let t : ℂ := 2 * ((n + 1 : ℕ) : ℂ)
  have ht : t / 2 = ((n + 1 : ℕ) : ℂ) := by
    dsimp [t]
    ring
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have harg : DifferentiableAt ℂ (fun s : ℂ => -s / 2) t := by fun_prop
  have hpow : DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) t :=
    harg.const_cpow (Or.inl hpi)
  have hlin : DifferentiableAt ℂ (fun s : ℂ => s / 2) t := by fun_prop
  have hgam : DifferentiableAt ℂ Complex.Gamma (t / 2) :=
    Complex.differentiableAt_Gamma (t / 2) (by
      intro m hm
      rw [ht] at hm
      have hm' : ((n + 1 : ℕ) : ℂ) = -(m : ℂ) := hm
      have hm'' : (n + 1 : ℕ) = -(m : ℤ) := by exact_mod_cast hm'
      omega)
  have hpowderiv : deriv (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) t =
      -Complex.log (Real.pi : ℂ) / 2 * (Real.pi : ℂ) ^ (-t / 2) := by
    rw [Complex.deriv_const_cpow harg (Real.pi : ℂ)]
    simp
    ring
  have hgamval : Complex.Gamma (t / 2) = (n.factorial : ℂ) := by
    rw [ht]
    push_cast
    exact Complex.Gamma_nat_eq_factorial n
  have hgamderiv : deriv Complex.Gamma (t / 2) =
      (n.factorial : ℂ) *
        ((-Real.eulerMascheroniConstant + (harmonic n : ℝ) : ℝ) : ℂ) := by
    rw [ht]
    push_cast
    exact Complex.deriv_Gamma_nat n
  have hcompderiv : deriv (fun s : ℂ => Complex.Gamma (s / 2)) t =
      deriv Complex.Gamma (t / 2) / 2 := by
    change deriv (Complex.Gamma ∘ (fun s : ℂ => s / 2)) t = _
    rw [deriv_comp t hgam hlin]
    simp
    ring
  have hcomp : DifferentiableAt ℂ
      (fun s : ℂ => Complex.Gamma (s / 2)) t :=
    DifferentiableAt.fun_comp' t (f := fun s : ℂ => s / 2)
      (g := Complex.Gamma) hgam hlin
  have hprodderiv := deriv_mul hpow hcomp
  have hpow_ne : (Real.pi : ℂ) ^ (-t / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  have hgam_ne : Complex.Gamma (t / 2) ≠ 0 := by
    rw [hgamval]
    exact_mod_cast Nat.factorial_ne_zero n
  have hfact : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  change deriv ((fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) *
      (fun s : ℂ => Complex.Gamma (s / 2))) t /
      ((Real.pi : ℂ) ^ (-t / 2) * Complex.Gamma (t / 2)) = _
  rw [hprodderiv, hpowderiv, hcompderiv, hgamderiv]
  rw [hgamval]
  field_simp [hpow_ne, hgam_ne, hfact]

private def completedNativeZetaSeriesCoefficients : ℕ → ℂ := fun _ => 1

private theorem completedNativeZeta_deriv_eq_logSeries {x : ℝ} (hx : 1 < x) :
    deriv riemannZeta (x : ℂ) =
      -LSeries (LSeries.logMul completedNativeZetaSeriesCoefficients) (x : ℂ) := by
  have hx' : (1 : ℂ).re < (x : ℂ).re := by simpa using hx
  have heq : (fun z : ℂ => LSeries completedNativeZetaSeriesCoefficients z) =ᶠ[nhds (x : ℂ)]
      riemannZeta := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hx'] with z hz
    rw [show completedNativeZetaSeriesCoefficients = (1 : ℕ → ℂ) by rfl]
    exact LSeries_one_eq_riemannZeta hz
  have hab : abscissaOfAbsConv completedNativeZetaSeriesCoefficients = 1 := by
    rw [show completedNativeZetaSeriesCoefficients = (1 : ℕ → ℂ) by rfl]
    exact LSeries.abscissaOfAbsConv_one
  have hL : deriv (LSeries completedNativeZetaSeriesCoefficients) (x : ℂ) =
      -LSeries (LSeries.logMul completedNativeZetaSeriesCoefficients) (x : ℂ) :=
    LSeries_deriv (by rw [hab]; exact_mod_cast hx)
  calc
    deriv riemannZeta (x : ℂ) =
        deriv (LSeries completedNativeZetaSeriesCoefficients) (x : ℂ) :=
      heq.deriv_eq.symm
    _ = _ := hL

theorem completedNativeZeta_deriv_over_zeta_tendsto_zero :
    Tendsto (fun x : ℝ => deriv riemannZeta (x : ℂ) / riemannZeta (x : ℂ))
      atTop (𝓝 (0 : ℂ)) := by
  have hcoeff : abscissaOfAbsConv completedNativeZetaSeriesCoefficients < ⊤ := by
    rw [show completedNativeZetaSeriesCoefficients = (1 : ℕ → ℂ) by
      funext n
      rfl, LSeries.abscissaOfAbsConv_one]
    exact EReal.coe_lt_top 1
  have hcoeffLog : abscissaOfAbsConv
      (LSeries.logMul completedNativeZetaSeriesCoefficients) < ⊤ := by
    rw [LSeries.abscissaOfAbsConv_logMul]
    exact hcoeff
  have hzetaSeries : Tendsto (fun x : ℝ => LSeries completedNativeZetaSeriesCoefficients x)
      atTop (𝓝 (1 : ℂ)) := by
    have h := LSeries.tendsto_atTop hcoeff
    simpa [completedNativeZetaSeriesCoefficients] using h
  have hlogSeries : Tendsto
      (fun x : ℝ => LSeries (LSeries.logMul completedNativeZetaSeriesCoefficients) x)
      atTop (𝓝 (0 : ℂ)) := by
    have h := LSeries.tendsto_atTop hcoeffLog
    simpa [completedNativeZetaSeriesCoefficients, LSeries.logMul] using h
  have hzeta : Tendsto (fun x : ℝ => riemannZeta (x : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    have heq : (fun x : ℝ => LSeries completedNativeZetaSeriesCoefficients x) =ᶠ[atTop]
        (fun x : ℝ => riemannZeta (x : ℂ)) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      have hx' : (1 : ℂ).re < (x : ℂ).re := by simpa using hx
      rw [show completedNativeZetaSeriesCoefficients = (1 : ℕ → ℂ) by rfl]
      exact LSeries_one_eq_riemannZeta hx'
    exact hzetaSeries.congr' heq
  have hderiv : Tendsto (fun x : ℝ => deriv riemannZeta (x : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    have heq : (fun x : ℝ => deriv riemannZeta (x : ℂ)) =ᶠ[atTop]
        (fun x : ℝ => -LSeries (LSeries.logMul completedNativeZetaSeriesCoefficients) (x : ℂ)) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      rw [completedNativeZeta_deriv_eq_logSeries hx]
    simpa using hlogSeries.neg.congr' heq.symm
  convert hderiv.div hzeta (by norm_num : (1 : ℂ) ≠ 0) using 1
  · ext x
    rfl
  · simp

theorem completedNativeHarmonicComparison_logDeriv_at_even_nat (n : ℕ) :
    let t : ℂ := 2 * ((n + 1 : ℕ) : ℂ)
    deriv completedNativeHarmonicComparison t /
        completedNativeHarmonicComparison t =
      1 / t + 1 / (t - 1) - (Real.log Real.pi : ℂ) / 2 +
        (-(Real.eulerMascheroniConstant : ℂ) + (harmonic n : ℂ)) / 2 +
        deriv riemannZeta t / riemannZeta t := by
  dsimp
  let t : ℂ := 2 * ((n + 1 : ℕ) : ℂ)
  have ht0 : t ≠ 0 := by
    dsimp [t]
    apply mul_ne_zero
    · norm_num
    · exact_mod_cast (Nat.succ_ne_zero n)
  have ht1 : t ≠ 1 := by
    dsimp [t]
    exact_mod_cast (by omega : 2 * (n + 1) ≠ 1)
  have htRe : 1 < t.re := by
    dsimp [t]
    norm_num [Complex.mul_re]
    exact_mod_cast (show 1 < 2 * (n + 1 : ℕ) by omega)
  have htRePos : 0 < t.re := lt_trans zero_lt_one htRe
  have hpoly : DifferentiableAt ℂ
      (fun s : ℂ => s * (s - 1) / 2) t := by fun_prop
  have hpowDiff : DifferentiableAt ℂ
      (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) t := by
    apply (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
    exact Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hgamDiff : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) t := by
    apply DifferentiableAt.fun_comp' t (f := fun s : ℂ => s / 2)
      (g := Complex.Gamma)
    · apply Complex.differentiableAt_Gamma
      intro m hm
      have hhalf : t / 2 = ((n + 1 : ℕ) : ℂ) := by
        dsimp [t]
        ring
      rw [hhalf] at hm
      have hm' : (n + 1 : ℕ) = -(m : ℤ) := by exact_mod_cast hm
      omega
    · fun_prop
  have hGammaDiff : DifferentiableAt ℂ Complex.Gammaℝ t := by
    change DifferentiableAt ℂ (fun s : ℂ =>
      (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) t
    exact hpowDiff.mul hgamDiff
  have hZetaDiff : DifferentiableAt ℂ riemannZeta t :=
    differentiableAt_riemannZeta (by simpa [t] using ht1)
  have hprodDiff : DifferentiableAt ℂ
      (fun s : ℂ => (s * (s - 1) / 2) * Complex.Gammaℝ s) t :=
    hpoly.mul hGammaDiff
  have hlocal : (fun s : ℂ => completedNativeHarmonicComparison s) =ᶠ[nhds t]
      (fun s => (s * (s - 1) / 2) * Complex.Gammaℝ s * riemannZeta s) := by
    filter_upwards [eventually_ne_nhds ht0, eventually_ne_nhds ht1,
      (isOpen_lt continuous_const continuous_re).mem_nhds htRePos] with s hs0 hs1 hsRe
    exact completedNativeHarmonicComparison_eq_gammaR_mul_zeta hs0 hs1 hsRe
  have hvalue := hlocal.eq_of_nhds
  have hderiv := hlocal.deriv_eq
  have hprodDeriv := deriv_mul hprodDiff hZetaDiff
  have hGderiv : deriv (fun s : ℂ => s * (s - 1) / 2) t = (2 * t - 1) / 2 := by
    rw [deriv_div_const]
    have hmul : deriv (fun s : ℂ => s * (s - 1)) t = (t - 1) + t := by
      calc
        deriv (fun s : ℂ => s * (s - 1)) t =
            deriv (fun s : ℂ => s) t * (t - 1) +
              t * deriv (fun s : ℂ => s - 1) t := by
                change deriv ((fun s : ℂ => s) * (fun s => s - 1)) t = _
                exact deriv_mul
                  (differentiableAt_id : DifferentiableAt ℂ (fun s => s) t)
                  ((differentiableAt_id : DifferentiableAt ℂ (fun s => s) t).sub_const 1)
        _ = (t - 1) + t := by simp
    rw [hmul]
    ring
  have hGval : t * (t - 1) / 2 ≠ 0 := by
    apply div_ne_zero
    · exact mul_ne_zero ht0 (sub_ne_zero.mpr ht1)
    · norm_num
  have hRval : Complex.Gammaℝ t ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos htRePos
  have hZval : riemannZeta t ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re htRe
  have hGammaLog := completedNativeGammaR_logDeriv_at_even_nat n
  have hRderiv : deriv Complex.Gammaℝ t =
      (-Complex.log (Real.pi : ℂ) / 2 +
        ((-Real.eulerMascheroniConstant + (harmonic n : ℝ) : ℝ) : ℂ) / 2) *
          Complex.Gammaℝ t := by
    have h : deriv Complex.Gammaℝ t / Complex.Gammaℝ t =
        -Complex.log (Real.pi : ℂ) / 2 +
          ((-Real.eulerMascheroniConstant + (harmonic n : ℝ) : ℝ) : ℂ) / 2 := by
      simpa [t] using hGammaLog
    field_simp [hRval] at h
    linear_combination (1 / 2 : ℂ) * h
  rw [hderiv, hvalue]
  change deriv ((fun s : ℂ => (s * (s - 1) / 2) * Complex.Gammaℝ s) *
      (fun s : ℂ => riemannZeta s)) t /
      ((t * (t - 1) / 2) * Complex.Gammaℝ t * riemannZeta t) = _
  have hGRderiv : deriv (fun s : ℂ => (s * (s - 1) / 2) * Complex.Gammaℝ s) t =
      deriv (fun s : ℂ => s * (s - 1) / 2) t * Complex.Gammaℝ t +
        (t * (t - 1) / 2) * deriv Complex.Gammaℝ t := by
    change deriv ((fun s : ℂ => s * (s - 1) / 2) * Complex.Gammaℝ) t = _
    exact deriv_mul hpoly hGammaDiff
  rw [hprodDeriv, hGRderiv, hGderiv, hRderiv]
  rw [Complex.ofReal_log Real.pi_pos.le]
  dsimp [t] at *
  field_simp [ht0, ht1, hGval, hRval, hZval]
  push_cast
  ring_nf

def completedNativeHarmonicLogDerivativeReal (n : ℕ) : ℝ :=
  (deriv completedNativeHarmonicComparison (2 * ((n + 1 : ℕ) : ℂ)) /
    completedNativeHarmonicComparison (2 * ((n + 1 : ℕ) : ℂ))).re

theorem completedNativeHarmonicLogDerivativeReal_eq (n : ℕ) :
    completedNativeHarmonicLogDerivativeReal n =
      1 / (2 * ((n + 1 : ℕ) : ℝ)) +
        1 / (2 * ((n + 1 : ℕ) : ℝ) - 1) - Real.log Real.pi / 2 +
        ((harmonic n : ℝ) - Real.eulerMascheroniConstant) / 2 +
        (deriv riemannZeta (2 * ((n + 1 : ℕ) : ℂ)) /
          riemannZeta (2 * ((n + 1 : ℕ) : ℂ))).re := by
  have h1 : (1 : ℂ) / (2 * ((n + 1 : ℕ) : ℂ)) =
      (((1 : ℝ) / (2 * ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
    have hd : (2 * ((n + 1 : ℕ) : ℂ)) =
        ((2 * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hd]
    calc
      (1 : ℂ) / ((2 * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) =
          ((1 : ℝ) : ℂ) / ((2 * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by simp
      _ = (((1 : ℝ) / (2 * ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) :=
        (Complex.ofReal_div _ _).symm
  have h2 : (1 : ℂ) / (2 * ((n + 1 : ℕ) : ℂ) - 1) =
      (((1 : ℝ) / (2 * ((n + 1 : ℕ) : ℝ) - 1) : ℝ) : ℂ) := by
    have hd : (2 * ((n + 1 : ℕ) : ℂ) - 1) =
        ((2 * ((n + 1 : ℕ) : ℝ) - 1 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hd]
    calc
      (1 : ℂ) / ((2 * ((n + 1 : ℕ) : ℝ) - 1 : ℝ) : ℂ) =
          ((1 : ℝ) : ℂ) / ((2 * ((n + 1 : ℕ) : ℝ) - 1 : ℝ) : ℂ) := by simp
      _ = (((1 : ℝ) / (2 * ((n + 1 : ℕ) : ℝ) - 1) : ℝ) : ℂ) :=
        (Complex.ofReal_div _ _).symm
  have h3 : (Real.log Real.pi : ℂ) / 2 =
      ((Real.log Real.pi / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have h4 : (-(Real.eulerMascheroniConstant : ℂ) + (harmonic n : ℂ)) / 2 =
      ((((harmonic n : ℝ) - Real.eulerMascheroniConstant) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [completedNativeHarmonicLogDerivativeReal,
    completedNativeHarmonicComparison_logDeriv_at_even_nat, h1, h2, h3, h4]
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]

/-- After removing the logarithmic main term, the real logarithmic derivative
has a finite limit. -/
theorem completedNativeHarmonicLogDerivativeReal_sub_logHalf_tendsto :
    Tendsto (fun n : ℕ => completedNativeHarmonicLogDerivativeReal n -
      Real.log (n : ℝ) / 2) atTop (𝓝 (-Real.log Real.pi / 2)) := by
  let t (n : ℕ) : ℝ := 2 * ((n + 1 : ℕ) : ℝ)
  have ht : Tendsto t atTop atTop := by
    apply tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ))
      (g := t) ?_ tendsto_natCast_atTop_atTop
    intro n
    dsimp [t]
    exact_mod_cast (show n ≤ 2 * (n + 1 : ℕ) by omega)
  have hζc : Tendsto
      (fun n : ℕ => deriv riemannZeta (2 * ((n + 1 : ℕ) : ℂ)) /
        riemannZeta (2 * ((n + 1 : ℕ) : ℂ))) atTop (𝓝 (0 : ℂ)) := by
    have h := completedNativeZeta_deriv_over_zeta_tendsto_zero.comp ht
    simpa [Function.comp_def, t, Nat.cast_add, Nat.cast_mul] using h
  have hζ : Tendsto
      (fun n : ℕ => (deriv riemannZeta (2 * ((n + 1 : ℕ) : ℂ)) /
        riemannZeta (2 * ((n + 1 : ℕ) : ℂ))).re) atTop (𝓝 0) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp hζc
    simpa [Function.comp_def] using h
  have hH : Tendsto
      (fun n : ℕ => (harmonic n : ℝ) - Real.log n -
        Real.eulerMascheroniConstant) atTop (𝓝 0) := by
    have h := Real.tendsto_harmonic_sub_log.sub_const Real.eulerMascheroniConstant
    simpa [sub_eq_add_neg, add_assoc] using h
  have hInv₁ : Tendsto (fun n : ℕ => (t n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ht
  have hInv₂ : Tendsto (fun n : ℕ => (t n - 1)⁻¹) atTop (𝓝 0) := by
    have ht' : Tendsto (fun n : ℕ => t n - 1) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1) ht
    exact tendsto_inv_atTop_zero.comp ht'
  have hErr : Tendsto (fun n : ℕ =>
      ((harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant) / 2)
      atTop (𝓝 0) := by
    simpa using hH.div_const 2
  have hConst : Tendsto (fun _ : ℕ => -Real.log Real.pi / 2) atTop
      (𝓝 (-Real.log Real.pi / 2)) := tendsto_const_nhds
  have hsum := (hInv₁.add hInv₂).add hConst
  have hsum := hsum.add hErr
  have hsum := hsum.add hζ
  have hformula : (fun n : ℕ => completedNativeHarmonicLogDerivativeReal n -
      Real.log (n : ℝ) / 2) =ᶠ[atTop]
      (fun n : ℕ => (t n)⁻¹ + (t n - 1)⁻¹ - Real.log Real.pi / 2 +
        ((harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant) / 2 +
        (deriv riemannZeta (2 * ((n + 1 : ℕ) : ℂ)) /
          riemannZeta (2 * ((n + 1 : ℕ) : ℂ))).re) := by
    filter_upwards with n
    rw [completedNativeHarmonicLogDerivativeReal_eq n]
    dsimp [t]
    ring
  have hsum' : Tendsto
      (fun n : ℕ => (t n)⁻¹ + (t n - 1)⁻¹ - Real.log Real.pi / 2 +
        ((harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant) / 2 +
        (deriv riemannZeta (2 * ((n + 1 : ℕ) : ℂ)) /
          riemannZeta (2 * ((n + 1 : ℕ) : ℂ))).re)
      atTop (𝓝 (-Real.log Real.pi / 2)) := by
    convert hsum using 1
    · ext n
      simp only [t, Nat.cast_add]
      ring
    · simp
  exact hsum'.congr' hformula.symm

/-- The gamma and zeta comparison grows logarithmically, hence sublinearly
along the positive even integers. -/
theorem completedNativeHarmonicLogDerivativeReal_div_succ_tendsto_zero :
    Tendsto (fun n : ℕ => completedNativeHarmonicLogDerivativeReal n /
      ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hN1 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa using tendsto_atTop_add_const_right atTop 1 hN
  have hlogNextRatio : Tendsto
      (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ) /
        ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hN1
  have hlogDiff : Tendsto
      (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))
      atTop (𝓝 0) := by
    simpa using Real.tendsto_log_nat_add_one_sub_log
  have hlogDiffRatio : Tendsto
      (fun n : ℕ => (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) /
        ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := hlogDiff.div_atTop hN1
  have hlogOverSucc : Tendsto
      (fun n : ℕ => Real.log (n : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have hsub := hlogNextRatio.sub hlogDiffRatio
    have heq : (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ) /
        ((n + 1 : ℕ) : ℝ) -
        (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) /
          ((n + 1 : ℕ) : ℝ)) =ᶠ[atTop]
        fun n => Real.log (n : ℝ) / ((n + 1 : ℕ) : ℝ) := by
      filter_upwards with n
      ring
    simpa using hsub.congr' heq
  have hrem := completedNativeHarmonicLogDerivativeReal_sub_logHalf_tendsto
  have hremOverSucc : Tendsto
      (fun n : ℕ => (completedNativeHarmonicLogDerivativeReal n -
        Real.log (n : ℝ) / 2) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    exact hrem.div_atTop hN1
  have hsum := (hlogOverSucc.div_const 2).add hremOverSucc
  have heq : (fun n : ℕ => completedNativeHarmonicLogDerivativeReal n /
      ((n + 1 : ℕ) : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => Real.log (n : ℝ) / ((n + 1 : ℕ) : ℝ) / 2 +
        (completedNativeHarmonicLogDerivativeReal n - Real.log (n : ℝ) / 2) /
          ((n + 1 : ℕ) : ℝ)) := by
    filter_upwards with n
    ring
  simpa using hsum.congr' heq.symm

theorem completedNativeHarmonicLogDerivativeReal_tendsto_atTop :
    Tendsto completedNativeHarmonicLogDerivativeReal atTop atTop := by
  let t (n : ℕ) : ℝ := 2 * ((n + 1 : ℕ) : ℝ)
  have ht : Tendsto t atTop atTop := by
    apply tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ))
      (g := t) ?_ tendsto_natCast_atTop_atTop
    intro n
    dsimp [t]
    exact_mod_cast (show n ≤ 2 * (n + 1 : ℕ) by omega)
  have hζc : Tendsto
      (fun n : ℕ => deriv riemannZeta (2 * ((n + 1 : ℕ) : ℂ)) /
        riemannZeta (2 * ((n + 1 : ℕ) : ℂ))) atTop (𝓝 (0 : ℂ)) := by
    have h := completedNativeZeta_deriv_over_zeta_tendsto_zero.comp ht
    simpa [Function.comp_def, t, Nat.cast_add, Nat.cast_mul] using h
  have hζ : Tendsto
      (fun n : ℕ => (deriv riemannZeta (2 * ((n + 1 : ℕ) : ℂ)) /
        riemannZeta (2 * ((n + 1 : ℕ) : ℂ))).re) atTop (𝓝 0) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp hζc
    simpa [Function.comp_def] using h
  have hH : Tendsto
      (fun n : ℕ => (harmonic n : ℝ) - Real.log n -
        Real.eulerMascheroniConstant) atTop (𝓝 0) := by
    have h := Real.tendsto_harmonic_sub_log.sub_const Real.eulerMascheroniConstant
    simpa [sub_eq_add_neg, add_assoc] using h
  have hInv₁ : Tendsto (fun n : ℕ => (t n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ht
  have hInv₂ : Tendsto (fun n : ℕ => (t n - 1)⁻¹) atTop (𝓝 0) := by
    have ht' : Tendsto (fun n : ℕ => t n - 1) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1) ht
    exact tendsto_inv_atTop_zero.comp ht'
  have hLog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLogHalf : Tendsto (fun n : ℕ => Real.log (n : ℝ) / 2) atTop atTop := by
    simpa [div_eq_mul_inv] using
      (hLog.atTop_mul_const (by norm_num : (0 : ℝ) < 2⁻¹))
  have hRest : Tendsto
      (fun n : ℕ => (t n)⁻¹ + (t n - 1)⁻¹ - Real.log Real.pi / 2 +
        ((harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant) / 2 +
        (deriv riemannZeta (2 * ((n + 1 : ℕ) : ℂ)) /
          riemannZeta (2 * ((n + 1 : ℕ) : ℂ))).re)
      atTop (𝓝 (-Real.log Real.pi / 2)) := by
    have hErr : Tendsto (fun n : ℕ =>
        ((harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant) / 2)
        atTop (𝓝 0) := by simpa using hH.div_const 2
    have hConst : Tendsto (fun _ : ℕ => -Real.log Real.pi / 2) atTop
        (𝓝 (-Real.log Real.pi / 2)) := tendsto_const_nhds
    have hsum := (hInv₁.add hInv₂).add hConst
    have hsum := hsum.add hErr
    convert hsum.add hζ using 1
    · ext n
      simp only [t, Nat.cast_add]
      ring
    · simp
  have hsum : Tendsto
      (fun n : ℕ => Real.log (n : ℝ) / 2 +
        ((t n)⁻¹ + (t n - 1)⁻¹ - Real.log Real.pi / 2 +
          ((harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant) / 2 +
          (deriv riemannZeta (2 * ((n + 1 : ℕ) : ℂ)) /
            riemannZeta (2 * ((n + 1 : ℕ) : ℂ))).re)) atTop atTop :=
    hLogHalf.atTop_add hRest
  have heq : completedNativeHarmonicLogDerivativeReal =ᶠ[atTop]
      (fun n : ℕ => Real.log (n : ℝ) / 2 +
        ((t n)⁻¹ + (t n - 1)⁻¹ - Real.log Real.pi / 2 +
          ((harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant) / 2 +
          (deriv riemannZeta (2 * ((n + 1 : ℕ) : ℂ)) /
            riemannZeta (2 * ((n + 1 : ℕ) : ℂ))).re)) := by
    filter_upwards with n
    rw [completedNativeHarmonicLogDerivativeReal_eq n]
    dsimp [t]
    ring
  exact hsum.congr' heq.symm

theorem completedNativeHarmonicComparison_even_pos (n : ℕ) :
    0 < completedNativeHarmonicComparison (2 * ((n + 1 : ℕ) : ℂ)) := by
  let t : ℝ := 2 * ((n + 1 : ℕ) : ℝ)
  have ht : 1 < t := by
    dsimp [t]
    exact_mod_cast (show 1 < 2 * (n + 1 : ℕ) by omega)
  have htc : 2 * ((n + 1 : ℕ) : ℂ) = (t : ℂ) := by
    dsimp [t]
    push_cast
    ring
  rw [htc]
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one ht))
  have ht1 : (t : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hfactor_real : 0 < t * (t - 1) / 2 := by positivity
  have hfactor_cast :
      (t : ℂ) * ((t : ℂ) - 1) / 2 = ((t * (t - 1) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hfactor : 0 < (t : ℂ) * ((t : ℂ) - 1) / 2 := by
    rw [hfactor_cast]
    exact Complex.pos_iff.mpr ⟨by simpa using hfactor_real, by simp⟩
  have hpow : (Real.pi : ℂ) ^ (-(t : ℂ) / 2) =
      ((Real.pi ^ (-t / 2) : ℝ) : ℂ) := by
    rw [show -(t : ℂ) / 2 = ((-t / 2 : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_cpow Real.pi_pos.le (-t / 2)]
  have hgamma_real : 0 < Real.pi ^ (-t / 2) * Real.Gamma (t / 2) := by
    exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  have hGammaEq : Complex.Gamma ((t : ℂ) / 2) = (Real.Gamma (t / 2) : ℂ) := by
    rw [show (t : ℂ) / 2 = ((t / 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.Gamma_ofReal _
  have hgamma : 0 < Complex.Gammaℝ (t : ℂ) := by
    rw [Complex.Gammaℝ_def, hpow, hGammaEq, ← Complex.ofReal_mul]
    exact Complex.pos_iff.mpr ⟨by simpa using hgamma_real, by simp⟩
  have hzeta : 0 < riemannZeta (t : ℂ) := by
    have h := riemannZeta_pos_of_one_lt ht
    simpa using h
  rw [completedNativeHarmonicComparison_eq_gammaR_mul_zeta ht0 ht1
    (by simpa using lt_trans zero_lt_one ht)]
  exact mul_pos (mul_pos hfactor hgamma) hzeta

private theorem completedNativeHarmonicComparison_even_ne_zero (n : ℕ) :
    completedNativeHarmonicComparison (2 * ((n + 1 : ℕ) : ℂ)) ≠ 0 :=
  ne_of_gt (completedNativeHarmonicComparison_even_pos n)

/-- A polynomial logarithmic derivative cannot have both logarithmic growth
and sublinear growth along the positive even integers. -/
theorem completedNativeHarmonicComparison_no_polynomial_log_derivative
    (P Q : Polynomial ℝ) (hQ : Q ≠ 0)
    (hQevent : ∀ᶠ n : ℕ in atTop,
      Q.eval (2 * ((n + 1 : ℕ) : ℝ)) ≠ 0)
    (hidentity : ∀ t : ℝ,
      Q.eval t * deriv completedNativeHarmonicComparison (t : ℂ) =
        P.eval t * completedNativeHarmonicComparison (t : ℂ)) :
    False := by
  let t (n : ℕ) : ℝ := 2 * ((n + 1 : ℕ) : ℝ)
  have ht : Tendsto t atTop atTop := by
    apply tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ))
      (g := t) ?_ tendsto_natCast_atTop_atTop
    intro n
    dsimp [t]
    exact_mod_cast (show n ≤ 2 * (n + 1 : ℕ) by omega)
  have hQevent' : ∀ᶠ n : ℕ in atTop, Q.eval (t n) ≠ 0 := by
    simpa [t] using hQevent
  have hratioEq : (fun n : ℕ => P.eval (t n) / Q.eval (t n)) =ᶠ[atTop]
      completedNativeHarmonicLogDerivativeReal := by
    filter_upwards [hQevent'] with n hQn
    let tc : ℂ := 2 * ((n + 1 : ℕ) : ℂ)
    have htc : (t n : ℂ) = tc := by
      dsimp [tc, t]
      push_cast
      ring
    have ht0 : tc ≠ 0 := by
      dsimp [tc]
      exact_mod_cast (show 2 * (n + 1 : ℕ) ≠ 0 by omega)
    have ht1 : tc ≠ 1 := by
      dsimp [tc]
      exact_mod_cast (show 2 * (n + 1 : ℕ) ≠ 1 by omega)
    have htRe1 : 1 < tc.re := by
      dsimp [tc]
      norm_num [Complex.mul_re]
      exact_mod_cast (show 1 < 2 * (n + 1 : ℕ) by omega)
    have hX : completedNativeHarmonicComparison tc ≠ 0 := by
      exact completedNativeHarmonicComparison_even_ne_zero n
    have hQcast : ((Q.eval (t n) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hQn
    have hId := hidentity (t n)
    rw [htc] at hId
    change ((Q.eval (t n) : ℝ) : ℂ) * deriv completedNativeHarmonicComparison tc =
      ((P.eval (t n) : ℝ) : ℂ) * completedNativeHarmonicComparison tc at hId
    have hlog : deriv completedNativeHarmonicComparison tc /
        completedNativeHarmonicComparison tc =
          (((P.eval (t n) : ℝ) / (Q.eval (t n) : ℝ) : ℝ) : ℂ) := by
      calc
        deriv completedNativeHarmonicComparison tc /
            completedNativeHarmonicComparison tc =
          (((Q.eval (t n) : ℝ) : ℂ) * deriv completedNativeHarmonicComparison tc) /
            (((Q.eval (t n) : ℝ) : ℂ) * completedNativeHarmonicComparison tc) := by
              field_simp [hQcast, hX]
        _ = (((P.eval (t n) : ℝ) : ℂ) * completedNativeHarmonicComparison tc) /
            (((Q.eval (t n) : ℝ) : ℂ) * completedNativeHarmonicComparison tc) := by rw [hId]
        _ = ((P.eval (t n) : ℝ) : ℂ) / ((Q.eval (t n) : ℝ) : ℂ) := by
              field_simp [hQcast, hX]
        _ = (((P.eval (t n) : ℝ) / (Q.eval (t n) : ℝ) : ℝ) : ℂ) :=
              (Complex.ofReal_div _ _).symm
    have hreal := congrArg Complex.re hlog
    simpa [completedNativeHarmonicLogDerivativeReal, tc, htc,
      Complex.ofReal_re] using hreal.symm
  have hratioTop : Tendsto (fun n : ℕ => P.eval (t n) / Q.eval (t n))
      atTop atTop := completedNativeHarmonicLogDerivativeReal_tendsto_atTop.congr'
        hratioEq.symm
  have hratioDivZero : Tendsto (fun n : ℕ =>
      (P.eval (t n) / Q.eval (t n)) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h := completedNativeHarmonicLogDerivativeReal_div_succ_tendsto_zero
    have heq : (fun n : ℕ =>
        (P.eval (t n) / Q.eval (t n)) / ((n + 1 : ℕ) : ℝ)) =ᶠ[atTop]
        (fun n : ℕ => completedNativeHarmonicLogDerivativeReal n /
          ((n + 1 : ℕ) : ℝ)) := by
      filter_upwards [hratioEq.symm] with n hn
      rw [hn]
    exact h.congr' heq.symm
  by_cases hlt : P.degree < Q.degree
  · have hlim := (Polynomial.div_tendsto_atTop_zero_of_degree_lt P Q hlt).comp ht
    have hlim' : Tendsto (fun n : ℕ => P.eval (t n) / Q.eval (t n))
        atTop (𝓝 0) := by simpa [Function.comp_def] using hlim
    exact (not_tendsto_nhds_of_tendsto_atTop hratioTop 0) hlim'
  · by_cases heq : P.degree = Q.degree
    · have hlim := (Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq
        P Q heq).comp ht
      have hlim' : Tendsto (fun n : ℕ => P.eval (t n) / Q.eval (t n))
          atTop (𝓝 (P.leadingCoeff / Q.leadingCoeff)) := by
        simpa [Function.comp_def] using hlim
      exact (not_tendsto_nhds_of_tendsto_atTop hratioTop
        (P.leadingCoeff / Q.leadingCoeff)) hlim'
    · have hdeg : Q.degree < P.degree := by
        have hle : Q.degree ≤ P.degree := le_of_not_gt hlt
        exact lt_of_le_of_ne hle (by
          intro h
          exact heq h.symm)
      have hdegNat : Q.natDegree < P.natDegree :=
        (Polynomial.natDegree_lt_natDegree_iff hQ).mpr hdeg
      let d : ℕ := P.natDegree - Q.natDegree
      let c : ℝ := P.leadingCoeff / Q.leadingCoeff
      have hd : 1 ≤ d := by
        dsimp [d]
        exact Nat.succ_le_of_lt (Nat.sub_pos_of_lt hdegNat)
      have heInt : (P.natDegree : ℤ) - (Q.natDegree : ℤ) = (d : ℤ) := by
        dsimp [d]
        exact (Nat.cast_sub (Nat.le_of_lt hdegNat)).symm
      have hequiv : (fun n : ℕ => P.eval (t n) / Q.eval (t n)) ~[atTop]
          (fun n : ℕ => c * (t n) ^ ((P.natDegree : ℤ) - (Q.natDegree : ℤ))) := by
        simpa [Function.comp_def, t, c] using
          (Polynomial.isEquivalent_atTop_div P Q).comp_tendsto ht
      let g (n : ℕ) : ℝ := c * (t n) ^ ((P.natDegree : ℤ) - (Q.natDegree : ℤ))
      have hgTop : Tendsto g atTop atTop := hequiv.tendsto_atTop_iff.mp hratioTop
      have hc : 0 < c := by
        by_contra hc
        have hc' : c ≤ 0 := le_of_not_gt hc
        have hgt : ∀ n : ℕ, g n ≤ 0 := by
          intro n
          apply mul_nonpos_of_nonpos_of_nonneg hc'
          apply zpow_nonneg
          dsimp [t]
          positivity
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hgTop.eventually_gt_atTop 0)
        have hpos := hN N le_rfl
        have hnonpos := hgt N
        linarith
      have hratioDivToG : Tendsto (fun n : ℕ => g n /
          ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
        obtain ⟨φ, hφ, hEq⟩ := hequiv.symm.exists_eq_mul
        have hratioDiv := hratioDivZero
        have hmul : Tendsto (fun n : ℕ => φ n *
            ((P.eval (t n) / Q.eval (t n)) / ((n + 1 : ℕ) : ℝ)))
            atTop (𝓝 0) := by
          simpa using hφ.mul hratioDiv
        have hEq' : (fun n : ℕ => g n / ((n + 1 : ℕ) : ℝ)) =ᶠ[atTop]
            (fun n : ℕ => φ n *
              ((P.eval (t n) / Q.eval (t n)) / ((n + 1 : ℕ) : ℝ))) := by
          filter_upwards [hEq] with n hn
          have hn' : g n = φ n *
              (P.eval (t n) / Q.eval (t n)) := by simpa [g] using hn
          rw [hn']
          ring
        exact hmul.congr' hEq'.symm
      have hbound : ∀ n : ℕ, 2 * c ≤ g n / ((n + 1 : ℕ) : ℝ) := by
        intro n
        have hn1 : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
        have htOne : 1 ≤ t n := by
          dsimp [t]
          exact_mod_cast (show 1 ≤ 2 * (n + 1 : ℕ) by omega)
        have hpow : t n ≤ (t n) ^ d := by
          calc
            t n = (t n) ^ 1 := by simp
            _ ≤ (t n) ^ d := pow_le_pow_right₀ htOne hd
        have hbase : 2 * c = c * t n / ((n + 1 : ℕ) : ℝ) := by
          dsimp [t]
          field_simp [ne_of_gt hn1]
        calc
          2 * c = c * t n / ((n + 1 : ℕ) : ℝ) := hbase
          _ ≤ c * (t n) ^ d / ((n + 1 : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpow hc.le) hn1.le
          _ = g n / ((n + 1 : ℕ) : ℝ) := by
            simp [g, heInt, zpow_natCast]
      have hsmall := hratioDivToG.eventually (Iio_mem_nhds hc)
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsmall
      have hltc := hN N le_rfl
      have hbig := hbound N
      linarith

/-- No finite relation among the canonical completed native logarithmic
derivative moments exists. The proof uses the exact Gamma derivative at the
positive even integers, not a hypothesis about real zeros. -/
theorem canonicalCompletedNativeLogDerivativeMoment_noFiniteMomentRelation :
    NoFiniteMomentRelation canonicalCompletedNativeLogDerivativeMoment := by
  intro s a haSupport hrel i
  by_contra hai
  have hi : i ∈ s := by
    by_contra hnot
    exact hai (haSupport i hnot)
  have hrel' : ∀ j : ℕ,
      ∑ k ∈ s, a k * canonicalCompletedNativeLogDerivativeMoment (k + j) = 0 := by
    intro j
    simpa [NoFiniteMomentRelation, Nat.zero_add] using hrel j
  have haNonzero : ∃ j, j ∈ s ∧ a j ≠ 0 := ⟨i, hi, hai⟩
  obtain ⟨D, A, hD, hEntire⟩ :=
    exists_completedNativeEntireResidual_real_coefficients_eq_zero_of_moment_relation
      s a haNonzero hrel'
  let Q := completedNativeHardyIntegerDenominatorReal D
  let P := completedNativeHardyIntegerNumeratorReal A
  have hmapD : Polynomial.map (algebraMap ℝ ℂ) D ≠ 0 :=
    (Polynomial.map_ne_zero_iff (RingHom.injective (algebraMap ℝ ℂ))).2 hD
  have hQmap : completedNativeHardyIntegerDenominator
      (Polynomial.map (algebraMap ℝ ℂ) D) ≠ 0 :=
    completedNativeHardyIntegerDenominator_ne_zero hmapD
  have hQ : Q ≠ 0 := by
    intro hzero
    have hmapQ : Polynomial.map (algebraMap ℝ ℂ) Q = 0 := by
      rw [hzero]
      simp
    apply hQmap
    rw [completedNativeHardyIntegerDenominator_eq_map]
    exact hmapQ
  have hQevent : ∀ᶠ n : ℕ in atTop,
      Q.eval (2 * ((n + 1 : ℕ) : ℝ)) ≠ 0 := by
    simpa [Q] using completedNativeHardyIntegerDenominatorReal_eventually_ne_zero D hD
  have hidentity : ∀ t : ℝ,
      Q.eval t * deriv completedNativeHarmonicComparison (t : ℂ) =
        P.eval t * completedNativeHarmonicComparison (t : ℂ) := by
    intro t
    simpa [Q, P] using completedNativeEntireResidual_realAxis_real D A hEntire t
  exact completedNativeHarmonicComparison_no_polynomial_log_derivative
    P Q hQ hQevent hidentity

end

end CarrySelfAdjointOperator
