import CarrySelfAdjointOperator.C2ClockCanonicalCumulants
import CarrySelfAdjointOperator.CompletedNativeTfvdSixSourceChiralDefect
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! The corrected C2 Mellin clock and the polarized material Green kernel. -/

open Set Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ComplexOrder Matrix MatrixOrder

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Camera CPFormal.Analytic.Cp

noncomputable section

def c2ClockComplexIntegrand (s : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (s - 1) * (c2ClockDensity x : ℂ)

def c2ClockComplexIntegral (s : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), c2ClockComplexIntegrand s x

private theorem c2ClockComplexIntegrand_integrableOn {s : ℂ}
    (hs : s.re ∈ Ioo (3 / 8 : ℝ) (5 / 8)) :
    IntegrableOn (c2ClockComplexIntegrand s) (Ioi 0) := by
  have hcont : ContinuousOn (c2ClockComplexIntegrand s) (Ioi 0) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hx₀ : 0 < x := hx
    have hpow := Complex.continuousAt_ofReal_cpow_const x (s - 1) (Or.inr hx₀.ne')
    have hd : ContinuousAt c2ClockDensity x := by
      unfold c2ClockDensity
      have hn : (1 : ℝ) + Real.exp x ≠ 0 := by positivity
      exact (continuousAt_const.add Real.continuous_exp.continuousAt).inv₀ hn
    exact hpow.mul (Complex.continuous_ofReal.continuousAt.comp hd)
  apply (c2ClockLogIntegrand_integrableOn 0 hs).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  have hx₀ : 0 < x := hx
  have hρ : 0 ≤ c2ClockDensity x := by unfold c2ClockDensity; positivity
  rw [c2ClockComplexIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx₀,
    Complex.norm_of_nonneg hρ]
  simp [c2ClockLogIntegrand, Complex.sub_re]

theorem c2ClockComplexIntegral_ofReal (s : ℝ) :
    c2ClockComplexIntegral (s : ℂ) = (c2ClockLogMoment 0 s : ℂ) := by
  unfold c2ClockComplexIntegral c2ClockLogMoment
  calc
    _ = ∫ x in Ioi (0 : ℝ), (c2ClockLogIntegrand 0 s x : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx₀ : 0 < x := hx
      simp only [c2ClockComplexIntegrand, c2ClockLogIntegrand, pow_zero, mul_one,
        Complex.ofReal_mul, Complex.ofReal_cpow hx₀.le, Complex.ofReal_sub, Complex.ofReal_one]
    _ = _ := integral_ofReal

theorem c2ClockComplexIntegral_eq_gamma_mul_nativeScalar {s : ℂ}
    (hs : s.re ∈ Ioo (3 / 8 : ℝ) (5 / 8)) :
    c2ClockComplexIntegral s =
      Complex.Gamma s * (1 - (2 : ℂ) ^ (1 - s)) * nativeScalar s := by
  let g := c2ClockComplexIntegrand s
  have hg : IntegrableOn g (Ioi 0) := c2ClockComplexIntegrand_integrableOn hs
  have hg₂ : IntegrableOn (fun x => g (2 * x)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff g 0 (by norm_num : (0 : ℝ) < 2)).2
      (by simpa using hg)
  have split : Set.EqOn (nativeC2MellinComplexGeometricSourceIntegrand s)
      (fun x => g x + (2 : ℂ) ^ (1 - s) * g (2 * x)) (Ioi 0) := by
    intro x hx
    have hx₀ : 0 < x := hx
    change (x : ℂ) ^ (s - 1) * (nativeC2MellinGeometricDensity x : ℂ) =
      g x + (2 : ℂ) ^ (1 - s) * g (2 * x)
    rw [nativeC2MellinGeometricDensity_eq_clock_add_dyadic hx₀, Complex.ofReal_add]
    simp only [g, c2ClockComplexIntegrand]
    have hp : (((2 * x : ℝ)) : ℂ) ^ (s - 1) =
        (2 : ℂ) ^ (s - 1) * (x : ℂ) ^ (s - 1) := by
      simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
        Complex.mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx₀.le (s - 1)
    rw [hp, ← mul_assoc ((2 : ℂ) ^ (1 - s)), ← mul_assoc ((2 : ℂ) ^ (1 - s)),
      ← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0),
      show 1 - s + (s - 1) = 0 by ring, Complex.cpow_zero, one_mul]
    ring
  have hmul : (2 : ℂ) ^ (1 - s) * (2 : ℂ)⁻¹ = (2 : ℂ) ^ (-s) := by
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ (by norm_num),
      show 1 - s + (-1) = -s by ring]
  have hI : (∫ x in Ioi (0 : ℝ), nativeC2MellinComplexGeometricSourceIntegrand s x) =
      (1 + (2 : ℂ) ^ (-s)) * c2ClockComplexIntegral s := by
    rw [setIntegral_congr_fun measurableSet_Ioi split, integral_add hg (hg₂.const_mul _),
      integral_const_mul, integral_comp_mul_left_Ioi g 0 (by norm_num : (0 : ℝ) < 2),
      mul_zero, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_ofNat,
      ← mul_assoc, hmul]
    change c2ClockComplexIntegral s + (2 : ℂ) ^ (-s) * c2ClockComplexIntegral s = _
    ring
  have hs₀ : 0 < s.re := by linarith [hs.1]
  have hdom : s ∈ nativeScalarDomain := by
    change -1 < s.re ∧ s.re < 1
    constructor <;> linarith [hs.1, hs.2]
  have hnorm : ‖(2 : ℂ) ^ (-s)‖ < 1 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hs₀)
  have hn : 1 + (2 : ℂ) ^ (-s) ≠ 0 := by
    intro he
    have he' : (2 : ℂ) ^ (-s) = -1 := by linear_combination he
    rw [he'] at hnorm
    simp at hnorm
  rw [nativeC2MellinComplexGeometricSourceIntegral_eq_gamma_bracketCharacteristic hs₀,
    bracketCharacteristic_eq_factor_mul_nativeScalar (camera := 2) (by norm_num) hdom,
    factor_two, c2Factor] at hI
  apply mul_left_cancel₀ hn
  rw [← hI]
  ring

/-- Original archimedean dressing with the Mellin Gamma and the remaining
dyadic camera factor in the denominator. -/
def c2ClockComplexCorrection (t : ℂ) : ℂ :=
  nativeXiCompletionFactor (-Complex.I * t) /
    (Complex.Gamma ((1 / 2 : ℂ) + t) * (1 - (2 : ℂ) ^ (1 - (1 / 2 + t))))

def c2ClockCorrectedCharacteristic (t : ℂ) : ℂ :=
  c2ClockComplexCorrection t * c2ClockComplexIntegral (1 / 2 + t)

theorem c2ClockCorrectedCharacteristic_eq_native {t : ℂ}
    (hs : ((1 / 2 : ℂ) + t).re ∈ Ioo (3 / 8 : ℝ) (5 / 8)) :
    c2ClockCorrectedCharacteristic t = completedNativeOperatorCharacteristic (-Complex.I * t) := by
  let s : ℂ := 1 / 2 + t
  have hs₀ : 0 < s.re := by linarith [hs.1]
  have hB : 1 - (2 : ℂ) ^ (1 - s) ≠ 0 := by
    have hp : 1 < ‖(2 : ℂ) ^ (1 - s)‖ := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), Complex.sub_re, Complex.one_re]
      exact Real.one_lt_rpow (by norm_num) (by linarith [hs.2])
    intro he
    have he' : (2 : ℂ) ^ (1 - s) = 1 := by linear_combination -he
    rw [he', norm_one] at hp
    exact (lt_irrefl _ hp)
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs₀
  have hparam : operatorHeightParameter (-Complex.I * t) = s := by
    unfold operatorHeightParameter s
    linear_combination -t * Complex.I_sq
  unfold c2ClockCorrectedCharacteristic c2ClockComplexCorrection
    completedNativeOperatorCharacteristic
  rw [hparam, c2ClockComplexIntegral_eq_gamma_mul_nativeScalar hs]
  change nativeXiCompletionFactor (-Complex.I * t) / (Complex.Gamma s *
      (1 - (2 : ℂ) ^ (1 - s))) * (Complex.Gamma s * (1 - (2 : ℂ) ^ (1 - s)) *
      nativeScalar s) = nativeXiCompletionFactor (-Complex.I * t) * nativeScalar s
  field_simp

/-- The local logarithm of the corrected Mellin clock, normalized at zero. -/
def c2ClockCorrectedLog (t : ℂ) : ℂ :=
  Complex.log (c2ClockCorrectedCharacteristic t / c2ClockCorrectedCharacteristic 0)

private theorem c2ClockCorrectedCharacteristic_eventuallyEq_native :
    c2ClockCorrectedCharacteristic =ᶠ[𝓝 0]
      fun t => completedNativeOperatorCharacteristic (-Complex.I * t) := by
  have h : ContinuousAt (fun t : ℂ => ((1 / 2 : ℂ) + t).re) 0 := by fun_prop
  have ht := h.preimage_mem_nhds
    (show Ioo (3 / 8 : ℝ) (5 / 8) ∈ 𝓝 (((1 / 2 : ℂ) + (0 : ℂ)).re) by
      apply Ioo_mem_nhds <;> norm_num)
  filter_upwards [ht] with t hs
  exact c2ClockCorrectedCharacteristic_eq_native hs

private theorem c2ClockCorrectedLog_rotated_response :
    (fun z => deriv c2ClockCorrectedLog (Complex.I * z)) =ᶠ[𝓝 0]
      fun z => (2 * Complex.I) *
        completedGreenNormalizedResponse completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z := by
  let F := completedNativeOperatorCharacteristic
  let g : ℂ → ℂ := fun t => F (-Complex.I * t) / F 0
  have hF₀ : F 0 ≠ 0 := completedNativeOperatorCharacteristic_zero_ne_zero
  have hg₀ : g 0 = 1 := by simp [g, hF₀]
  have hmass := c2ClockCorrectedCharacteristic_eventuallyEq_native.eq_of_nhds
  simp only [mul_zero] at hmass
  have hlog : c2ClockCorrectedLog =ᶠ[𝓝 0] fun t => Complex.log (g t) := by
    filter_upwards [c2ClockCorrectedCharacteristic_eventuallyEq_native] with t ht
    simp only [c2ClockCorrectedLog, g, ht, hmass, F]
  have hg : AnalyticAt ℂ g 0 := by
    have hlin : AnalyticAt ℂ (fun t : ℂ => -Complex.I * t) 0 := by fun_prop
    have hbase : AnalyticAt ℂ F (-Complex.I * (0 : ℂ)) := by
      simpa [F] using completedNativeOperatorCharacteristic_analyticAt
        zero_mem_completedNativeHeightDomain
    exact (hbase.comp hlin).div analyticAt_const hF₀
  have hslit : ∀ᶠ t in 𝓝 0, g t ∈ Complex.slitPlane :=
    hg.continuousAt.preimage_mem_nhds
      (Complex.isOpen_slitPlane.mem_nhds (by simp [hg₀]))
  obtain ⟨U, hUlog, hUopen, hU₀⟩ := mem_nhds_iff.mp hlog
  have hrot : Tendsto (fun z : ℂ => Complex.I * z) (𝓝 0) (𝓝 0) := by
    have h : ContinuousAt (fun z : ℂ => Complex.I * z) 0 := by fun_prop
    simpa using h.tendsto
  have hF : AnalyticAt ℂ F 0 := completedNativeOperatorCharacteristic_analyticAt
    zero_mem_completedNativeHeightDomain
  filter_upwards [hrot.eventually (hUopen.mem_nhds hU₀), hrot.eventually hslit,
    hF.eventually_analyticAt, hF.continuousAt.eventually_ne hF₀] with z hzU hzSlit hzAnal hzNonzero
  have hloc : c2ClockCorrectedLog =ᶠ[𝓝 (Complex.I * z)]
      fun t => Complex.log (g t) := by
    filter_upwards [hUopen.mem_nhds hzU] with t ht
    exact hUlog ht
  have harg : -Complex.I * (Complex.I * z) = z := by
    linear_combination -z * Complex.I_sq
  have hF' := hzAnal.differentiableAt.hasDerivAt
  rw [← harg] at hF'
  have hlin := (hasDerivAt_id (Complex.I * z)).const_mul (-Complex.I)
  have hd := ((hF'.comp (Complex.I * z) hlin).div_const (F 0)).clog hzSlit
  have hd' : HasDerivAt (fun t => Complex.log (g t))
      (deriv F z * -Complex.I / F 0 / (F z / F 0)) (Complex.I * z) := by
    simpa only [Function.comp_def, id_eq, mul_one, harg, g] using hd
  rw [hloc.deriv_eq, hd'.deriv, completedGreenNormalizedResponse,
    completedNativeOperatorBoundaryCompanion_eq_neg_deriv]
  change deriv F z * -Complex.I / F 0 / (F z / F 0) =
    (2 * Complex.I) * (-deriv F z / (2 * F z))
  field_simp

/-- Polarization uses conjugation on the first **height** before rotation.
The divided derivative on the collision set is Mathlib's removable dslope. -/
def c2ClockPolarizedKernel (z w : ℂ) : ℂ :=
  (1 / 2 : ℂ) * dslope (deriv c2ClockCorrectedLog)
    (Complex.I * conj z) (Complex.I * w)

private theorem c2Clock_dslope_rotate (f : ℂ → ℂ) (a b : ℂ) :
    dslope (fun z => f (Complex.I * z)) a b =
      Complex.I * dslope f (Complex.I * a) (Complex.I * b) := by
  rcases eq_or_ne b a with rfl | hab
  · simp only [dslope_same]
    rw [deriv_comp_mul_left, smul_eq_mul, mul_comm]
  · have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have hneq : Complex.I * b ≠ Complex.I * a := fun h => hab (mul_left_cancel₀ hI h)
    rw [dslope_of_ne _ hab, dslope_of_ne _ hneq]
    simp only [slope, smul_eq_mul]
    rw [← mul_sub]
    field_simp [sub_ne_zero.mpr hab, hI]

private theorem c2Clock_dslope_locallyEq {f g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (heq : Set.EqOn f g U) {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) :
    dslope f a b = dslope g a b := by
  rcases eq_or_ne b a with rfl | h
  · simp only [dslope_same]
    have hh : f =ᶠ[𝓝 b] g := by
      filter_upwards [hU.mem_nhds ha] with x hx
      exact heq hx
    exact hh.deriv_eq
  · rw [dslope_of_ne _ h, dslope_of_ne _ h]
    simp only [slope, heq ha, heq hb]

/-- One neighborhood works for every pair, including the collision set. -/
theorem c2ClockPolarizedKernel_eq_dslope_near_zero :
    ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧
      ∀ z w : ℂ, conj z ∈ U → w ∈ U →
        c2ClockPolarizedKernel z w = canonicalCompletedNativePolarizedDslopeKernel z w := by
  let R := completedGreenNormalizedResponse completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion
  obtain ⟨U, heq, hU, hU₀⟩ :=
    mem_nhds_iff.mp c2ClockCorrectedLog_rotated_response
  refine ⟨U, hU, hU₀, fun z w hz hw => ?_⟩
  have h := c2Clock_dslope_locallyEq hU
    (show Set.EqOn (fun z => deriv c2ClockCorrectedLog (Complex.I * z))
      (fun z => (2 * Complex.I) * R z) U from fun _ hx => heq hx) hz hw
  rw [c2Clock_dslope_rotate] at h
  have hc : dslope (fun z => (2 * Complex.I) * R z) (conj z) w =
      (2 * Complex.I) * dslope R (conj z) w := by
    rcases eq_or_ne w (conj z) with rfl | hsep
    · simp only [dslope_same, deriv_const_mul_field]
    · rw [dslope_of_ne _ hsep, dslope_of_ne _ hsep]
      simp only [slope, smul_eq_mul, vsub_eq_sub]
      ring
  rw [hc] at h
  have h₂ : dslope (deriv c2ClockCorrectedLog) (Complex.I * conj z) (Complex.I * w) =
      2 * dslope R (conj z) w := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    rw [h]
    ring
  unfold c2ClockPolarizedKernel canonicalCompletedNativePolarizedDslopeKernel
  change (1 / 2 : ℂ) * dslope (deriv c2ClockCorrectedLog) _ _ = dslope R _ _
  rw [h₂]
  ring

/-- The corrected clock kernel equals the full six-source material readout,
with both arguments preserved, at every cutoff on a regular neighborhood. -/
theorem c2ClockPolarizedKernel_eq_sixSource_near_zero :
    ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧
      ∀ (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
        (S : Finset NativeGpreBoundaryContext) (z w : ℂ),
        z ∈ U → w ∈ U → w ≠ conj z →
        c2ClockPolarizedKernel z w =
          nativeC3SeededClockTfvdSixSourceOffDiagonalKernelReadout
            M z w q hqpos.le hq1 S := by
  obtain ⟨V, hV, hV₀, hK⟩ := c2ClockPolarizedKernel_eq_dslope_near_zero
  have hF : ∀ᶠ z : ℂ in 𝓝 0, completedNativeOperatorCharacteristic z ≠ 0 :=
    completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
      completedNativeOperatorCharacteristic_zero_ne_zero
  obtain ⟨W, hWF, hW, hW₀⟩ := mem_nhds_iff.mp hF
  let U := (V ∩ (conj ⁻¹' V)) ∩ (W ∩ completedNativeHeightDomain)
  have hconj : Continuous (conj : ℂ → ℂ) := Complex.continuous_conj
  refine ⟨U, (hV.inter (hV.preimage hconj)).inter
    (hW.inter isOpen_completedNativeHeightDomain), ?_, ?_⟩
  · exact ⟨⟨hV₀, by simpa using hV₀⟩, hW₀, zero_mem_completedNativeHeightDomain⟩
  · intro M q hqpos hq1 S z w hz hw hsep
    rw [hK z w hz.1.2 hw.1.1]
    exact (nativeC3SeededClockTfvdSixSourceOffDiagonalKernelReadout_eq_polarizedDslope
      M q hqpos hq1 S hz.2.2 hw.2.2 (hWF hz.2.1) (hWF hw.2.1) hsep).symm

/-- The two-index material jet is read in the original clock cumulants.
Odd total degree vanishes; the two nonzero sectors are interlaced. -/
theorem c2ClockSixSourceForwardDifference_tendsto_correctedCumulant
    (M p r : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    Tendsto
      (fun k : ℕ => completedGreenKernelForwardDifference
        (nativeC3SeededClockTfvdSixSourceRealAxisKernelReadout M q hqpos.le hq1 S)
        (canonicalGreenJetStep k) p r)
      atTop
      (𝓝 (polarizedGreenMomentCoefficient
        (fun n => (-1 : ℝ) ^ n * correctedCumulantEntry c2ClockCorrectedCumulant n) p r)) := by
  have hm : canonicalCompletedNativeLogDerivativeMoment =
      (fun n => (-1 : ℝ) ^ n * correctedCumulantEntry c2ClockCorrectedCumulant n) :=
    funext c2ClockCanonicalMoment_eq_correctedCumulant
  rw [← hm]
  exact nativeC3SeededClockTfvdSixSourceKernelForwardDifference_tendsto_moment
    M p r q hqpos hq1 S

def c2ClockRadialSampleMatrix (k N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j : Fin N => c2ClockPolarizedKernel
    (canonicalCompletedC3RadialTiltPoint k i)
    (canonicalCompletedC3RadialTiltPoint k j))

/-- In each fixed radial dimension, the corrected clock and material
matrices agree for all sufficiently small tilts, including their diagonal
entries on the upper half-plane. -/
theorem c2ClockPolarizedKernel_eventually_eq_sixSource_radial
    (M N : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ∀ᶠ k : ℕ in atTop,
      c2ClockRadialSampleMatrix k N =
      nativeC3SeededClockTfvdSixSourceRadialSampleMatrix M q hqpos.le hq1 S k N := by
  obtain ⟨U, hU, hU₀, hbridge⟩ := c2ClockPolarizedKernel_eq_sixSource_near_zero
  have hpoints : ∀ᶠ k : ℕ in atTop, ∀ i : Fin N,
      canonicalCompletedC3RadialTiltPoint k i ∈ U := by
    rw [Filter.eventually_all]
    intro i
    exact (canonicalCompletedC3RadialTiltPoint_tendsto_zero i).eventually (hU.mem_nhds hU₀)
  filter_upwards [hpoints] with k hk
  ext i j
  simp only [c2ClockRadialSampleMatrix,
    nativeC3SeededClockTfvdSixSourceRadialSampleMatrix, Matrix.of_apply]
  exact hbridge M q hqpos hq1 S _ _ (hk i) (hk j)
    (sub_ne_zero.mp (canonicalCompletedC3RadialTilt_separation_ne_zero k i j))

/-- The concrete positive Gram to compare with is the incident Cauchy Gram.
The missing inequality is contractivity of the returned multiplier on
the whole finite span, including pairs of distinct incident vectors. -/
theorem c2ClockPolarizedKernel_radial_posSemidef_iff_return
    (M N : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ∀ᶠ k : ℕ in atTop,
      (c2ClockRadialSampleMatrix k N).PosSemidef ↔
      CanonicalCompletedNativeRadialChiralMultiplierContractiveAt k N := by
  filter_upwards [c2ClockPolarizedKernel_eventually_eq_sixSource_radial
    M N q hqpos hq1 S, canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N]
    with k hk hregular
  rw [hk]
  exact nativeC3SeededClockTfvdSixSourceRadialSampleMatrix_posSemidef_iff_chiralMultiplierContractive
    M q hqpos hq1 S k N hregular

/-- The known two-point contraction transfers to the clock's own kernel. -/
theorem c2ClockRadialSampleMatrix_two_eventually_posSemidef :
    ∀ᶠ k : ℕ in atTop, (c2ClockRadialSampleMatrix k 2).PosSemidef := by
  filter_upwards [c2ClockPolarizedKernel_radial_posSemidef_iff_return
    0 2 (1 / 2) (by norm_num) (by norm_num) ∅,
    canonicalCompletedNativeChiralTwoPoint_contractive_eventually] with k h e
  exact h.mpr e

set_option maxHeartbeats 500000 in
/-- Exact quadratic energy defect in the original incident and returned
states, for every coefficient vector on the same sufficiently small grid. -/
theorem c2ClockPolarizedKernel_radial_energy
    (M N : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ∀ᶠ k : ℕ in atTop, ∀ c : Fin N → ℂ,
      2 * (star c ⬝ᵥ (c2ClockRadialSampleMatrix k N *ᵥ c)).re =
        ‖∑ i, (c i * completedNativeNormalizedPositiveChiralAmplitude
          (canonicalCompletedC3RadialTiltPoint k i)) •
          completedNativeRadialChiralCauchyState k i‖ ^ 2 -
        ‖∑ i, (c i * completedNativeNormalizedPositiveChiralAmplitude
          (canonicalCompletedC3RadialTiltPoint k i)) •
          completedNativeRadialChiralMultiplierState k i‖ ^ 2 := by
  filter_upwards [c2ClockPolarizedKernel_eventually_eq_sixSource_radial
    M N q hqpos hq1 S, canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N]
    with k hk hregular c
  rw [hk]
  exact nativeC3SeededClockTfvdSixSourceRadialSampleQuadratic_re_eq_chiralInput_sub_output
    M q hqpos hq1 S k N hregular c

end

end CarrySelfAdjointOperator
