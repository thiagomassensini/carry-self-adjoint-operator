import CarrySelfAdjointOperator.CompletedNativeWeylMoments
import CarrySelfAdjointOperator.GlobalKernelProbe
import Mathlib.Tactic

/-!
# Real-axis Weyl moments of the completed native characteristic

The completed characteristic is real on the centered height axis.  Its
complex Taylor jets at the origin can therefore be read without loss through
ordinary real derivatives.  This file uses that fact to construct the unique
real division-free logarithmic moment sequence recursively.

No zero set, spectral height, confinement statement, or positivity premise is
used here.
-/

open scoped BigOperators

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- Conjugating a real centered height reflects its spectral parameter. -/
theorem operatorHeightParameter_neg_ofReal_eq_conj (t : ℝ) :
    operatorHeightParameter (-(t : ℂ)) =
      (starRingEnd ℂ) (operatorHeightParameter (t : ℂ)) := by
  apply Complex.ext <;> simp [operatorHeightParameter]

/-- The archimedean completion factor respects the same reflected
conjugation on the real height axis. -/
theorem nativeXiCompletionFactor_neg_ofReal_eq_conj (t : ℝ) :
    nativeXiCompletionFactor (-(t : ℂ)) =
      (starRingEnd ℂ) (nativeXiCompletionFactor (t : ℂ)) := by
  unfold nativeXiCompletionFactor
  dsimp only
  rw [operatorHeightParameter_neg_ofReal_eq_conj]
  simp only [map_mul, map_sub, map_one, map_ofNat, map_div₀]
  rw [← Complex.exp_conj, ← Complex.Gamma_conj]
  congr 2 <;>
    simp only [map_neg, map_mul, map_div₀, map_ofNat,
      Complex.conj_ofReal]

/-- Before using centered evenness, reflection of a real height is already
complex conjugation of the completed characteristic. -/
theorem completedNativeOperatorCharacteristic_neg_ofReal_eq_conj (t : ℝ) :
    completedNativeOperatorCharacteristic (-(t : ℂ)) =
      (starRingEnd ℂ)
        (completedNativeOperatorCharacteristic (t : ℂ)) := by
  have hstrip : operatorHeightParameter (t : ℂ) ∈ genuineCriticalStrip := by
    constructor <;> norm_num [operatorHeightParameter]
  have hnegstrip :
      operatorHeightParameter (-(t : ℂ)) ∈ genuineCriticalStrip := by
    constructor <;> norm_num [operatorHeightParameter]
  unfold completedNativeOperatorCharacteristic
  rw [nativeScalar_eq_riemannZeta hnegstrip,
    nativeScalar_eq_riemannZeta hstrip,
    nativeXiCompletionFactor_neg_ofReal_eq_conj,
    operatorHeightParameter_neg_ofReal_eq_conj,
    riemannZeta_conj]
  simp

/-- The completed native characteristic is real-valued on the whole centered
height axis. -/
theorem completedNativeOperatorCharacteristic_ofReal_im_eq_zero (t : ℝ) :
    (completedNativeOperatorCharacteristic (t : ℂ)).im = 0 := by
  have hstrip : operatorHeightParameter (t : ℂ) ∈ genuineCriticalStrip := by
    constructor <;> norm_num [operatorHeightParameter]
  have heven := completedNativeOperatorCharacteristic_neg
    (z := (t : ℂ)) hstrip
  have hconj := completedNativeOperatorCharacteristic_neg_ofReal_eq_conj t
  have hfixed :
      completedNativeOperatorCharacteristic (t : ℂ) =
        (starRingEnd ℂ)
          (completedNativeOperatorCharacteristic (t : ℂ)) := by
    exact heven.symm.trans hconj
  have him := congrArg Complex.im hfixed
  rw [Complex.conj_im] at him
  linarith

/-- The real height axis belongs to the natural centered-height domain. -/
theorem ofReal_mem_completedNativeHeightDomain (t : ℝ) :
    (t : ℂ) ∈ completedNativeHeightDomain := by
  change operatorHeightParameter (t : ℂ) ∈ genuineCriticalStrip
  constructor <;> norm_num [operatorHeightParameter]

/-- Restriction of a holomorphic scalar to the real axis preserves its first
derivative, with no phase factor. -/
theorem deriv_comp_ofReal_eq
    {f : ℂ → ℂ} {t : ℝ}
    (hf : DifferentiableAt ℂ f (t : ℂ)) :
    deriv (fun u : ℝ ↦ f (u : ℂ)) t = deriv f (t : ℂ) := by
  exact hf.hasDerivAt.comp_ofReal.deriv

private theorem differentiableOn_iteratedDeriv_of_differentiableOn
    {f : ℂ → ℂ} {domain : Set ℂ}
    (hf : DifferentiableOn ℂ f domain)
    (hdomain : IsOpen domain) (order : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv order f) domain := by
  induction order with
  | zero => simpa using hf
  | succ order ih =>
      rw [show order + 1 = Nat.succ order by omega, iteratedDeriv_succ]
      exact ih.deriv hdomain

/-- Every real derivative of the restricted completed characteristic equals
the corresponding complex Taylor derivative. -/
theorem iteratedDeriv_completedNativeOperatorCharacteristic_comp_ofReal
    (order : ℕ) (t : ℝ) :
    iteratedDeriv order
        (fun u : ℝ ↦ completedNativeOperatorCharacteristic (u : ℂ)) t =
      iteratedDeriv order completedNativeOperatorCharacteristic (t : ℂ) := by
  have hdiff : DifferentiableOn ℂ completedNativeOperatorCharacteristic
      completedNativeHeightDomain := by
    intro z hz
    exact (completedNativeOperatorCharacteristic_analyticAt hz).differentiableAt.differentiableWithinAt
  induction order generalizing t with
  | zero => simp
  | succ order ih =>
      have hfunction :
          iteratedDeriv order
              (fun u : ℝ ↦ completedNativeOperatorCharacteristic (u : ℂ)) =
            fun u : ℝ ↦
              iteratedDeriv order completedNativeOperatorCharacteristic
                (u : ℂ) := by
        funext u
        exact ih u
      have houter : DifferentiableAt ℂ
          (iteratedDeriv order completedNativeOperatorCharacteristic)
          (t : ℂ) :=
        (differentiableOn_iteratedDeriv_of_differentiableOn
          hdiff isOpen_completedNativeHeightDomain order).differentiableAt
            (isOpen_completedNativeHeightDomain.mem_nhds
              (ofReal_mem_completedNativeHeightDomain t))
      rw [iteratedDeriv_succ, hfunction,
        deriv_comp_ofReal_eq houter, ← iteratedDeriv_succ]

/-- Every complex Taylor derivative on the real height axis is real. -/
theorem iteratedDeriv_completedNativeOperatorCharacteristic_zero_im
    (order : ℕ) (t : ℝ := 0) :
    (iteratedDeriv order completedNativeOperatorCharacteristic (t : ℂ)).im =
      0 := by
  induction order generalizing t with
  | zero =>
      simpa using completedNativeOperatorCharacteristic_ofReal_im_eq_zero t
  | succ order ih =>
      let outer : ℂ → ℂ :=
        iteratedDeriv order completedNativeOperatorCharacteristic
      have hdiff : DifferentiableOn ℂ completedNativeOperatorCharacteristic
          completedNativeHeightDomain := by
        intro z hz
        exact (completedNativeOperatorCharacteristic_analyticAt hz).differentiableAt.differentiableWithinAt
      have houter : DifferentiableAt ℂ outer (t : ℂ) :=
        (differentiableOn_iteratedDeriv_of_differentiableOn
          hdiff isOpen_completedNativeHeightDomain order).differentiableAt
            (isOpen_completedNativeHeightDomain.mem_nhds
              (ofReal_mem_completedNativeHeightDomain t))
      have hcomplex : HasDerivAt (fun u : ℝ ↦ outer (u : ℂ))
          (deriv outer (t : ℂ)) t :=
        houter.hasDerivAt.comp_ofReal
      have hreal : HasDerivAt
          (fun u : ℝ ↦ ((outer (u : ℂ)).re : ℂ))
          ((deriv outer (t : ℂ)).re : ℂ) t :=
        houter.hasDerivAt.real_of_complex.ofReal_comp
      have hfunctions :
          (fun u : ℝ ↦ outer (u : ℂ)) =
            fun u : ℝ ↦ ((outer (u : ℂ)).re : ℂ) := by
        funext u
        apply Complex.ext
        · simp
        · exact ih u
      rw [← hfunctions] at hreal
      have hderivReal :
          deriv outer (t : ℂ) = ((deriv outer (t : ℂ)).re : ℂ) :=
        hcomplex.unique hreal
      have him := congrArg Complex.im hderivReal
      simpa [outer, iteratedDeriv_succ] using him

/-- The even Taylor coefficient is exactly the complex coercion of its real
part. -/
theorem completedNativeEvenCharacteristicCoefficient_eq_ofReal_re (n : ℕ) :
    completedNativeEvenCharacteristicCoefficient n =
      ((completedNativeEvenCharacteristicCoefficient n).re : ℂ) := by
  apply Complex.ext
  · simp
  · unfold completedNativeEvenCharacteristicCoefficient
      completedGreenTaylorJet
    simp [Complex.mul_im,
      Nat.factorial_ne_zero]
    exact iteratedDeriv_completedNativeOperatorCharacteristic_zero_im (2 * n)

/-- Concrete real coefficient sequence underlying the completed even
characteristic. -/
def completedNativeRealEvenCharacteristicCoefficient (n : ℕ) : ℝ :=
  (completedNativeEvenCharacteristicCoefficient n).re

@[simp] theorem completedNativeEvenCharacteristicCoefficient_eq_real
    (n : ℕ) :
    completedNativeEvenCharacteristicCoefficient n =
      (completedNativeRealEvenCharacteristicCoefficient n : ℂ) := by
  exact completedNativeEvenCharacteristicCoefficient_eq_ofReal_re n

/-- The real constant coefficient remains nonzero. -/
theorem completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero :
    completedNativeRealEvenCharacteristicCoefficient 0 ≠ 0 := by
  intro hzero
  apply completedNativeEvenCharacteristicCoefficient_zero_ne_zero
  rw [completedNativeEvenCharacteristicCoefficient_eq_real, hzero]
  simp

/-- Canonical root-free recurrence for the completed logarithmic Weyl
moments. -/
def canonicalCompletedNativeLogDerivativeMoment : ℕ → ℝ
  := Nat.lt_wfRel.wf.fix fun n previous =>
      (-((n + 1 : ℕ) : ℝ) *
          completedNativeRealEvenCharacteristicCoefficient (n + 1) -
        ∑ k : Fin n,
          previous k k.isLt *
            completedNativeRealEvenCharacteristicCoefficient (n - k)) /
        completedNativeRealEvenCharacteristicCoefficient 0

/-- Unfolding equation for the well-founded real moment recurrence. -/
theorem canonicalCompletedNativeLogDerivativeMoment_eq (n : ℕ) :
    canonicalCompletedNativeLogDerivativeMoment n =
      (-((n + 1 : ℕ) : ℝ) *
          completedNativeRealEvenCharacteristicCoefficient (n + 1) -
        ∑ k ∈ Finset.range n,
          canonicalCompletedNativeLogDerivativeMoment k *
            completedNativeRealEvenCharacteristicCoefficient (n - k)) /
        completedNativeRealEvenCharacteristicCoefficient 0 := by
  rw [canonicalCompletedNativeLogDerivativeMoment, WellFounded.fix_eq]
  congr 2
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [dif_pos (Finset.mem_range.mp hk)]

/-- The recursively constructed real moments satisfy the exact
division-free logarithmic derivative identity. -/
theorem canonicalCompletedNativeLogDerivativeMoment_real_recurrence
    (n : ℕ) :
    completedNativeRealEvenCharacteristicCoefficient 0 *
          canonicalCompletedNativeLogDerivativeMoment n +
        ∑ k ∈ Finset.range n,
          canonicalCompletedNativeLogDerivativeMoment k *
            completedNativeRealEvenCharacteristicCoefficient (n - k) =
      -((n + 1 : ℕ) : ℝ) *
        completedNativeRealEvenCharacteristicCoefficient (n + 1) := by
  rw [canonicalCompletedNativeLogDerivativeMoment_eq]
  field_simp [completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero]
  ring

/-- Existence of the concrete real completed-native Weyl moment sequence. -/
theorem canonicalCompletedNativeLogDerivativeMoment_isMomentSequence :
    IsCompletedNativeLogDerivativeMomentSequence
      canonicalCompletedNativeLogDerivativeMoment := by
  intro n
  simp_rw [completedNativeEvenCharacteristicCoefficient_eq_real]
  norm_cast
  convert canonicalCompletedNativeLogDerivativeMoment_real_recurrence n using 1
  all_goals ring

/-- The canonical recursive sequence is the unique real moment sequence of
the completed characteristic. -/
theorem completedNativeLogDerivativeMoment_eq_canonical
    {moments : ℕ → ℝ}
    (hrel : IsCompletedNativeLogDerivativeMomentSequence moments) :
    moments = canonicalCompletedNativeLogDerivativeMoment :=
  hrel.unique
    canonicalCompletedNativeLogDerivativeMoment_isMomentSequence

end

end CarrySelfAdjointOperator
