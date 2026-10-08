import CarrySelfAdjointOperator.CompletedNativeChiralReturnSevenBoundaryFace

/-!
# Complete seven-coordinate boundary regularization in the original Cauchy carrier

Higher Euler coordinates are reconstructed, never discarded at a finite step.
The entire seven-term vector prefix is synthesized before the mixed readout.
Only the boundary limit removes the higher coordinate powers. No sign is assumed.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology ChiralReturn
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Higher Euler boundary coordinates are determined by the same inverse,
not discarded. -/
def radialSevenHigherBoundaryCoefficient (m : ℕ) (a : Fin 7) : ℝ :=
  ∑ i : Fin 7, (((i : ℕ)+1 : ℕ) : ℝ)^m * radialSevenBoundaryInverseCoefficients i a

/-- Continuous regularization of EVERY higher boundary coordinate. -/
def radialSevenRegularizedBoundary (h : ℝ) (x : Fin 7 → ℂ) (m : ℕ) : ℂ :=
  if hm : m < 7 then x ⟨m, hm⟩ else
    ∑ a : Fin 7, ((h^(m-(a : ℕ)) * radialSevenHigherBoundaryCoefficient m a : ℝ) : ℂ) * x a

theorem radialSevenRegularizedBoundary_eq (h : ℝ) (hh : h ≠ 0) (x : Fin 7 → ℂ) (m : ℕ) :
    radialSevenRegularizedBoundary h x m =
      ((h^m : ℝ) : ℂ) * radialEulerBoundaryJet (radialSevenNormalizedBoundaryInput h x) m := by
  unfold radialSevenRegularizedBoundary
  split_ifs with hm
  · have hs := congrFun (radialSevenScaledBoundary_input h hh x) ⟨m, hm⟩
    simpa only [radialSevenScaledBoundary, Fin.val_mk] using hs.symm
  · unfold radialEulerBoundaryJet radialSevenNormalizedBoundaryInput radialSevenBoundaryReconstruct
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    unfold radialSevenHigherBoundaryCoefficient
    simp only [Complex.ofReal_mul, Complex.ofReal_sum, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    have hp : h^(m-(a : ℕ)) * h^(a : ℕ) = h^m := by rw [← pow_add]; congr 1; omega
    have hpa : h^(a : ℕ) ≠ 0 := pow_ne_zero _ hh
    have he : h^(m-(a : ℕ)) = h^m * (h^(a : ℕ))⁻¹ := (eq_mul_inv_iff_mul_eq₀ hpa).mpr hp
    rw [he]
    push_cast
    ring

theorem radialSevenRegularizedBoundary_zero (x : Fin 7 → ℂ) (m : ℕ) :
    radialSevenRegularizedBoundary 0 x m = nativeSourceSevenBoundaryExtension x m := by
  unfold radialSevenRegularizedBoundary nativeSourceSevenBoundaryExtension
  split_ifs with hm
  · rfl
  · apply Finset.sum_eq_zero
    intro a _
    have hp : m-(a : ℕ) ≠ 0 := by omega
    simp [hp]

theorem radialSevenRegularizedBoundary_continuous (m : ℕ) :
    Continuous (fun y : ℝ × (Fin 7 → ℂ) => radialSevenRegularizedBoundary y.1 y.2 m) := by
  unfold radialSevenRegularizedBoundary
  split_ifs with hm <;> fun_prop

/-- The COMPLETE original signed tower at a finite step, including higher
Euler coordinates. It is not the limiting face substituted early. -/
def radialSevenRegularizedBoundaryEnergy (h : ℝ) (x : Fin 7 → ℂ) : ℝ :=
  2 * ∑ j ∈ Finset.range 7, (-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j *
    (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
      (conj (radialSevenRegularizedBoundary h x a) *
        radialSevenRegularizedBoundary h x (2*j-a)).re)

theorem radialSevenRegularizedBoundaryEnergy_zero (x : Fin 7 → ℂ) :
    radialSevenRegularizedBoundaryEnergy 0 x = nativeSourceSevenBoundaryEnergy x := by
  unfold radialSevenRegularizedBoundaryEnergy
  simp_rw [radialSevenRegularizedBoundary_zero]
  exact (nativeSourceSevenBoundaryEnergy_eq_alternating_green x).symm

theorem radialSevenRegularizedBoundaryEnergy_continuous :
    Continuous (fun y : ℝ × (Fin 7 → ℂ) => radialSevenRegularizedBoundaryEnergy y.1 y.2) := by
  have hb (a b : ℕ) : Continuous (fun y : ℝ × (Fin 7 → ℂ) =>
      (conj (radialSevenRegularizedBoundary y.1 y.2 a) *
        radialSevenRegularizedBoundary y.1 y.2 b).re) :=
    Complex.continuous_re.comp ((Complex.continuous_conj.comp
      (radialSevenRegularizedBoundary_continuous a)).mul
        (radialSevenRegularizedBoundary_continuous b))
  unfold radialSevenRegularizedBoundaryEnergy
  fun_prop

/-- All higher boundary coordinates participate in the exact polynomial
source energy; only at h=0 do they vanish in the regular boundary chart. -/
theorem radialSevenSourcePrefix_energy (k : ℕ) (h : ℝ) (hh : h ≠ 0)
    (hkh : ((k : ℝ)+1)*h = 1) (x : Fin 7 → ℂ) :
    4 * (inner ℂ (radialIncidentSynthesis k 7 (radialSevenNormalizedBoundaryInput h x))
      (∑ j ∈ Finset.range 7,
        (((-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j * h^(2*j+1) : ℝ) : ℂ) •
          radialEulerPowerSynthesis k 7 (2*j+1) (radialSevenNormalizedBoundaryInput h x))).re =
      radialSevenRegularizedBoundaryEnergy h x := by
  let d := radialSevenNormalizedBoundaryInput h x
  have hc (j a : ℕ) (ha : a < 2*j+1) :
      (conj (radialSevenRegularizedBoundary h x a) *
        radialSevenRegularizedBoundary h x (2*j-a)).re =
      h^(2*j) * (conj (radialEulerBoundaryJet d a) * radialEulerBoundaryJet d (2*j-a)).re := by
    rw [radialSevenRegularizedBoundary_eq h hh x a,
      radialSevenRegularizedBoundary_eq h hh x (2*j-a)]
    have hp : h^a * h^(2*j-a) = h^(2*j) := by rw [← pow_add]; congr 1; omega
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero]
    change _ = _
    linear_combination
      (radialEulerBoundaryJet d a).re * (radialEulerBoundaryJet d (2*j-a)).re * hp +
      (radialEulerBoundaryJet d a).im * (radialEulerBoundaryJet d (2*j-a)).im * hp
  simp only [inner_sum, inner_smul_right, Complex.re_sum, Complex.re_ofReal_mul,
    radialSevenRegularizedBoundaryEnergy]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hs : (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
      (conj (radialSevenRegularizedBoundary h x a) *
        radialSevenRegularizedBoundary h x (2*j-a)).re) =
      h^(2*j) * (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
        (conj (radialEulerBoundaryJet d a) * radialEulerBoundaryJet d (2*j-a)).re) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [hc j a (Finset.mem_range.mp ha)]
    ring
  rw [hs]
  have hpow : ((k : ℝ)+1)*h^(2*j+1) = h^(2*j) := by
    rw [pow_succ]
    linear_combination h^(2*j) * hkh
  have hg := radialEulerPower_odd_green_energy k 7 j d
  linear_combination 2 * ((-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j) * h^(2*j+1) * hg +
    2 * ((-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j) *
      (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
        (conj (radialEulerBoundaryJet d a) * radialEulerBoundaryJet d (2*j-a)).re) * hpow


/-- Boundary limit of the fully reconstructed signed tower, not a readout
postulated from source coefficients. -/
theorem radialSevenRegularizedBoundaryEnergy_tendsto (x : Fin 7 → ℂ) :
    Tendsto (fun h : ℝ => radialSevenRegularizedBoundaryEnergy h x)
      (nhds 0) (nhds (nativeSourceSevenBoundaryEnergy x)) := by
  have hpair : Continuous (fun h : ℝ => (h,x)) :=
    continuous_id.prodMk continuous_const
  have hc := radialSevenRegularizedBoundaryEnergy_continuous.comp hpair
  have ht : Tendsto (fun h : ℝ => radialSevenRegularizedBoundaryEnergy h x)
      (nhds 0) (nhds (radialSevenRegularizedBoundaryEnergy 0 x)) :=
    hc.continuousAt.tendsto
  exact ht.mono_right (le_of_eq (congrArg nhds (radialSevenRegularizedBoundaryEnergy_zero x)))

/-- The actual vector prefix in the SAME Cauchy carrier converges to the
complete seven-coordinate face. Every original i/j cross is retained. -/
theorem radialSevenSourcePrefix_energy_tendsto (x : Fin 7 → ℂ) :
    Tendsto (fun k : ℕ =>
      4 * (inner ℂ
        (radialIncidentSynthesis k 7 (radialSevenNormalizedBoundaryInput (radialFourSourceStep k) x))
        (∑ j ∈ Finset.range 7,
          (((-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j *
            (radialFourSourceStep k)^(2*j+1) : ℝ) : ℂ) •
            radialEulerPowerSynthesis k 7 (2*j+1)
              (radialSevenNormalizedBoundaryInput (radialFourSourceStep k) x))).re)
      atTop (nhds (nativeSourceSevenBoundaryEnergy x)) := by
  have he : (fun k : ℕ =>
      4 * (inner ℂ
        (radialIncidentSynthesis k 7 (radialSevenNormalizedBoundaryInput (radialFourSourceStep k) x))
        (∑ j ∈ Finset.range 7,
          (((-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j *
            (radialFourSourceStep k)^(2*j+1) : ℝ) : ℂ) •
            radialEulerPowerSynthesis k 7 (2*j+1)
              (radialSevenNormalizedBoundaryInput (radialFourSourceStep k) x))).re) =
      fun k => radialSevenRegularizedBoundaryEnergy (radialFourSourceStep k) x := by
    funext k
    apply radialSevenSourcePrefix_energy k _ (radialFourSourceStep_pos k).ne'
    unfold radialFourSourceStep
    exact mul_inv_cancel₀ (by positivity)
  rw [he]
  exact (radialSevenRegularizedBoundaryEnergy_tendsto x).comp radialFourSourceStep_tendsto_zero

end
end CarrySelfAdjointOperator
