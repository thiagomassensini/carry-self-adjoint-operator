import CarrySelfAdjointOperator.CameraReturnVarianceEnergyBalance
import NativeCarrySpectralWeyl.Infinite.WeylUnbounded
import NativeCarrySpectralWeyl.Camera.QuantitativeTail
import NativeCarrySpectralWeyl.Camera.CommonZeroSet
import NativeCarrySpectralWeyl.Limits.FiniteDefectCovariance

/-!
# Centered all-bases realization and native camera cutoff convergence

The centered Naimark vectors and logarithmic multiplier are reused unchanged.
Their full cross Gram gives an isometric extension on the existing camera
completion. Native scalar readouts coalesce after the proved camera factors,
including a shared physical cutoff with complete centers. The full camera
covariance retains distinct directions: cameras 3 and 5 have limiting unit
separation squared equal to two. No new spectral generator is introduced.
-/

open scoped ENNReal MeasureTheory RealInnerProductSpace BigOperators Topology
open Set MeasureTheory Filter
namespace CarrySelfAdjointOperator
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Camera NativeCarrySpectralWeyl.Limits
noncomputable section
set_option autoImplicit false

theorem integral_centeredLog_cross_min {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    ∫ x in 0..min b c,
      (logarithmicCoordinate x - Real.log b) *
        (logarithmicCoordinate x - Real.log c) = min b c := by
  have hp : 0 < min b c := lt_min hb hc
  have htwo : IntervalIntegrable
      (fun x : ℝ => logarithmicCoordinate x ^ 2) volume 0 (min b c) :=
    intervalIntegrable_centeredLogSq_zero hp
  have hone : IntervalIntegrable logarithmicCoordinate volume 0 (min b c) :=
    intervalIntegrable_centeredLog_zero
  calc
    _ = ∫ x in 0..min b c, logarithmicCoordinate x ^ 2 -
        (Real.log b + Real.log c) * logarithmicCoordinate x +
        Real.log b * Real.log c := by
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    _ = (min b c) * (1 + Real.log (min b c) ^ 2) -
        (Real.log b + Real.log c) * ((min b c) * Real.log (min b c)) +
        (min b c) * (Real.log b * Real.log c) := by
      rw [intervalIntegral.integral_add (htwo.sub (hone.const_mul _))
          intervalIntegrable_const,
        intervalIntegral.integral_sub htwo (hone.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      simp only [logarithmicCoordinate, integral_centeredLogSq_zero hp,
        integral_centeredLog_zero hp, sub_zero, smul_eq_mul]
    _ = min b c := by
      rcases le_total b c with h | h
      · rw [min_eq_left h]
        ring
      · rw [min_eq_right h]
        ring

theorem inner_centeredNaimarkCameraVector (b c : CameraIndex) :
    inner ℝ (centeredNaimarkCameraVector b) (centeredNaimarkCameraVector c) =
      gramKernel b c := by
  have hpoint :
      (fun x => inner ℝ (centeredNaimarkCameraVector b x)
        (centeredNaimarkCameraVector c x)) =ᵐ[positiveLebesgueMeasure]
      (cameraInterval b ∩ cameraInterval c).indicator
        (fun x => (logarithmicCoordinate x -
          Real.log (cameraSlope (cameraLabel b) : ℝ)) *
          (logarithmicCoordinate x - Real.log (cameraSlope (cameraLabel c) : ℝ)) *
          periodicMeanKernel b c) := by
    filter_upwards [centeredNaimarkCameraVector_coeFn b,
      centeredNaimarkCameraVector_coeFn c] with x hb hc
    rw [hb, hc]
    by_cases hxb : x ∈ cameraInterval b
    <;> by_cases hxc : x ∈ cameraInterval c
    <;> simp [hxb, hxc, Set.mem_inter_iff, real_inner_smul_left,
      real_inner_smul_right, inner_kolmogorovVector]
    ring
  have hmeas := (cameraInterval_measurable b).inter (cameraInterval_measurable c)
  have hsubset : cameraInterval b ∩ cameraInterval c ⊆ Ioi 0 :=
    Set.inter_subset_left.trans (cameraInterval_subset_positive b)
  rw [L2.inner_def, integral_congr_ae hpoint, integral_indicator hmeas,
    positiveLebesgueMeasure, Measure.restrict_restrict hmeas,
    inter_eq_left.mpr hsubset, integral_mul_const]
  have hb : (0 : ℝ) < cameraSlope (cameraLabel b) := by exact_mod_cast cameraSlope_pos b
  have hc : (0 : ℝ) < cameraSlope (cameraLabel c) := by exact_mod_cast cameraSlope_pos c
  simp only [cameraInterval, Ioc_inter_Ioc, max_self]
  rw [← intervalIntegral.integral_of_le (le_of_lt (lt_min hb hc)),
    integral_centeredLog_cross_min hb hc]
  simp [gramKernel]

theorem finiteCamera_normalizedResultant_tendsto {b : ℕ} (hb : 2 ≤ b) (t : ℝ) :
    Tendsto (fun M => finiteBracketCharacteristic b M (nativeLine t) /
      factor b (nativeLine t)) atTop (nhds (nativeScalar (nativeLine t))) := by
  have hd : nativeLine t ∈ bracketDomain := by simp [bracketDomain]; norm_num
  have h := (finiteBracketCharacteristic_tendstoLocallyUniformlyOn hb).tendsto_at hd
  have hs : nativeLine t ∈ nativeScalarDomain := by simp [nativeScalarDomain]; norm_num
  have hr := h.div_const (factor b (nativeLine t))
  rw [bracketCharacteristic_eq_factor_mul_nativeScalar hb hs,
    mul_div_cancel_left₀ _ (factor_nativeLine_ne_zero hb t)] at hr
  exact hr
/-- Synthesis of the already existing centered profiles in the existing Naimark space. -/
def centeredCameraCoreMap : CameraFinsupp →ₗ[ℝ] NaimarkSpace :=
  Finsupp.linearCombination ℝ centeredNaimarkCameraVector

theorem centeredCameraCoreMap_inner (u v : CameraFinsupp) :
    inner ℝ (centeredCameraCoreMap u) (centeredCameraCoreMap v) = gramForm u v := by
  classical
  rw [gramForm_comm]
  simp only [centeredCameraCoreMap, Finsupp.linearCombination_apply,
    Finsupp.sum_inner, Finsupp.inner_sum, real_inner_smul_left,
    real_inner_smul_right, inner_centeredNaimarkCameraVector, gramForm]
  apply Finsupp.sum_congr
  intro c hc
  apply Finsupp.sum_congr
  intro b hb
  rw [gramKernel_comm b c]
  ring

theorem centeredCameraCoreMap_norm (u : CameraFinsupp) :
    ‖centeredCameraCoreMap u‖ = ‖u‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner,
    centeredCameraCoreMap_inner, cameraFinsupp_inner_eq_gramForm]

def centeredCameraCoreIsometry : CameraFinsupp →ₗᵢ[ℝ] NaimarkSpace where
  toLinearMap := centeredCameraCoreMap
  norm_map' := centeredCameraCoreMap_norm

/-- Continuous extension of the centered profiles, using the existing CameraHilbert. -/
def centeredCameraExtension : CameraHilbert →L[ℝ] NaimarkSpace :=
  centeredCameraCoreIsometry.toContinuousLinearMap.extend
    cameraEmbedding.toContinuousLinearMap

theorem centeredCameraExtension_cameraEmbedding (u : CameraFinsupp) :
    centeredCameraExtension (cameraEmbedding u) = centeredCameraCoreIsometry u :=
  ContinuousLinearMap.extend_eq
    centeredCameraCoreIsometry.toContinuousLinearMap cameraEmbedding_denseRange
      cameraEmbedding.isometry.isUniformInducing u

theorem centeredCameraExtension_norm (x : CameraHilbert) :
    ‖centeredCameraExtension x‖ = ‖x‖ := by
  refine cameraEmbedding_denseRange.induction_on
    (p := fun y => ‖centeredCameraExtension y‖ = ‖y‖) x ?_ ?_
  · exact isClosed_eq
      (continuous_norm.comp centeredCameraExtension.continuous) continuous_norm
  · intro u
    rw [centeredCameraExtension_cameraEmbedding, centeredCameraCoreIsometry.norm_map,
      cameraEmbedding.norm_map]

/-- The Gram-preserving centered realization on the full existing Hilbert completion.
This is an isometric analysis map, not a new spectral generator. -/
def centeredCameraIsometry : CameraHilbert →ₗᵢ[ℝ] NaimarkSpace where
  toLinearMap := centeredCameraExtension.toLinearMap
  norm_map' := centeredCameraExtension_norm

theorem centeredCameraIsometry_cameraVector (b : CameraIndex) :
    centeredCameraIsometry (cameraVector b) = centeredNaimarkCameraVector b := by
  change centeredCameraExtension (cameraEmbedding (Finsupp.single b 1)) = _
  rw [centeredCameraExtension_cameraEmbedding]
  change centeredCameraCoreMap (Finsupp.single b 1) = _
  simp [centeredCameraCoreMap]

/-- Every Hilbert readout travels with its Riesz vector, with all cross products. -/
theorem centeredCameraIsometry_readout (q x : CameraHilbert) :
    inner ℝ (centeredCameraIsometry q) (centeredCameraIsometry x) = inner ℝ q x :=
  centeredCameraIsometry.inner_map_map q x

theorem finiteCamera_normalizedResultant_pairwise_tendsto
    {b c : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c) (t : ℝ) :
    Tendsto (fun M => finiteBracketCharacteristic b M (nativeLine t) /
      factor b (nativeLine t) -
      finiteBracketCharacteristic c M (nativeLine t) / factor c (nativeLine t))
      atTop (nhds 0) := by
  simpa using (finiteCamera_normalizedResultant_tendsto hb t).sub
    (finiteCamera_normalizedResultant_tendsto hc t)

/-- The complete six-camera covariance converges, while the normalized 3--5
squared separation tends to two. The normalization uses the exact limiting
camera energies 6 and 20; all finite seed/tail coefficients are retained. -/
theorem finiteCamera_three_five_separation_tendsto {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun M =>
      finiteCoefficientCovariance (resolventWeight z) M sixCamera 1 1 / 6 +
      finiteCoefficientCovariance (resolventWeight z) M sixCamera 3 3 / 20 -
      2 * finiteCoefficientCovariance (resolventWeight z) M sixCamera 1 3 /
        Real.sqrt (6 * 20))
      atTop (nhds 2) := by
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  have h (i j : Fin 6) := tendsto_resolvent_finiteCoefficientCovariance_apply
    hz (by norm_num : 0 < 420) hcamera sixCamera_commonPeriod i j
  have h33 : Tendsto (fun M =>
      finiteCoefficientCovariance (resolventWeight z) M sixCamera 1 1)
      atTop (nhds 6) := by
    simpa [sixCameraGram_eq, sixCameraGram, sixCameraGramRat] using h 1 1
  have h55 : Tendsto (fun M =>
      finiteCoefficientCovariance (resolventWeight z) M sixCamera 3 3)
      atTop (nhds 20) := by
    simpa [sixCameraGram_eq, sixCameraGram, sixCameraGramRat, Matrix.cons_val] using h 3 3
  have h35 : Tendsto (fun M =>
      finiteCoefficientCovariance (resolventWeight z) M sixCamera 1 3)
      atTop (nhds 0) := by
    simpa [sixCameraGram_eq, sixCameraGram, sixCameraGramRat, Matrix.cons_val] using h 1 3
  convert ((h33.div_const 6).add (h55.div_const 20)).sub
    ((h35.const_mul 2).div_const (Real.sqrt (6 * 20))) using 1
  norm_num

/-- Increasing a physical cutoff supplies arbitrarily many complete centers. -/
theorem completeCameraCenterCount_tendsto {b : ℕ} (hb : 2 ≤ b) :
    Tendsto (fun N : ℕ => (N - cameraBoundaryWidth b) / cameraSlope b)
      atTop atTop := by
  have hs : 0 < cameraSlope b := by
    by_cases h : b = 2
    · simp [h]
    · rw [cameraSlope_of_ne_two h]
      omega
  refine tendsto_atTop.2 fun K => eventually_atTop.2
    ⟨K * cameraSlope b + cameraBoundaryWidth b, ?_⟩
  intro N hN
  exact (Nat.le_div_iff_mul_le hs).2 (Nat.le_sub_of_add_le hN)

/-- The same common scalar is reached at a shared physical cutoff, with a
different number of complete centers in each camera. Seeds are complete
eventually; no partial center is required. -/
theorem finiteCamera_normalizedPhysicalCutoff_tendsto
    {b : ℕ} (hb : 2 ≤ b) (t : ℝ) :
    Tendsto (fun N => finiteBracketCharacteristic b
      ((N - cameraBoundaryWidth b) / cameraSlope b) (nativeLine t) /
      factor b (nativeLine t)) atTop (nhds (nativeScalar (nativeLine t))) :=
  (finiteCamera_normalizedResultant_tendsto hb t).comp
    (completeCameraCenterCount_tendsto hb)

/-- All normalized cameras coalesce in the scalar readout at common physical
cutoff. This does not identify the Hilbert camera vectors. -/
theorem finiteCamera_normalizedPhysicalCutoff_pairwise_tendsto
    {b c : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c) (t : ℝ) :
    Tendsto (fun N =>
      finiteBracketCharacteristic b ((N - cameraBoundaryWidth b) / cameraSlope b)
        (nativeLine t) / factor b (nativeLine t) -
      finiteBracketCharacteristic c ((N - cameraBoundaryWidth c) / cameraSlope c)
        (nativeLine t) / factor c (nativeLine t))
      atTop (nhds 0) := by
  simpa using (finiteCamera_normalizedPhysicalCutoff_tendsto hb t).sub
    (finiteCamera_normalizedPhysicalCutoff_tendsto hc t)

theorem finiteSixCamera_covariance_entry_tendsto
    {z : ℂ} (hz : z.im ≠ 0) (i j : Fin 6) :
    Tendsto (fun M => finiteCoefficientCovariance (resolventWeight z) M sixCamera i j)
      atTop (nhds (sixCameraGram i j)) := by
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro k
    fin_cases k <;> norm_num [sixCamera]
  simpa only [sixCameraGram_eq] using
    tendsto_resolvent_finiteCoefficientCovariance_apply
      hz (by norm_num : 0 < 420) hcamera sixCamera_commonPeriod i j

/-- Even after individual unit normalization, cameras 3 and 5 retain a
nonzero limiting separation. The full finite coefficients define the norms. -/
theorem finiteCamera_three_five_unitSeparation_tendsto {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun M => 2 -
      2 * finiteCoefficientCovariance (resolventWeight z) M sixCamera 1 3 /
        Real.sqrt (finiteCoefficientCovariance (resolventWeight z) M sixCamera 1 1 *
          finiteCoefficientCovariance (resolventWeight z) M sixCamera 3 3))
      atTop (nhds 2) := by
  have h33 : Tendsto (fun M =>
      finiteCoefficientCovariance (resolventWeight z) M sixCamera 1 1)
      atTop (nhds 6) := by
    simpa [sixCameraGram, sixCameraGramRat] using
      finiteSixCamera_covariance_entry_tendsto hz 1 1
  have h55 : Tendsto (fun M =>
      finiteCoefficientCovariance (resolventWeight z) M sixCamera 3 3)
      atTop (nhds 20) := by
    simpa [sixCameraGram, sixCameraGramRat, Matrix.cons_val] using
      finiteSixCamera_covariance_entry_tendsto hz 3 3
  have h35 : Tendsto (fun M =>
      finiteCoefficientCovariance (resolventWeight z) M sixCamera 1 3)
      atTop (nhds 0) := by
    simpa [sixCameraGram, sixCameraGramRat, Matrix.cons_val] using
      finiteSixCamera_covariance_entry_tendsto hz 1 3
  have hsqrt := (Real.continuous_sqrt.tendsto (6 * 20)).comp (h33.mul h55)
  have h := (show Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) from tendsto_const_nhds).sub
    ((h35.const_mul 2).div hsqrt (by positivity : Real.sqrt ((6 : ℝ) * 20) ≠ 0))
  simpa [Function.comp_def] using h

/-- Before the first complete center, the center count stays on its initial plateau. -/
theorem completeCameraCenterCount_initialPlateau {b N : ℕ} (hb : 2 ≤ b)
    (hN : N < cameraSlope b + cameraBoundaryWidth b) :
    (N - cameraBoundaryWidth b) / cameraSlope b = 0 := by
  have hs : 0 < cameraSlope b := by
    by_cases h : b = 2
    · simp [h]
    · rw [cameraSlope_of_ne_two h]
      omega
  apply Nat.div_eq_of_lt
  omega

/-- All real and imaginary source pairings travel through the same centered
isometry. This preserves a specified readout without identifying different
readouts or discarding either quadrature. -/
theorem centeredCameraIsometry_twoQuadrature_readout
    (q x y : CameraHilbert) :
    (inner ℝ (centeredCameraIsometry q) (centeredCameraIsometry x) : ℂ) +
        Complex.I * (inner ℝ (centeredCameraIsometry q)
          (centeredCameraIsometry y) : ℂ) =
      (inner ℝ q x : ℂ) + Complex.I * (inner ℝ q y : ℂ) := by
  rw [centeredCameraIsometry_readout, centeredCameraIsometry_readout]

/-- Raw camera differences retain their geometric multipliers in the limit. -/
theorem finiteCamera_rawDifference_tendsto
    {b c : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c) (t : ℝ) :
    Tendsto (fun M => finiteBracketCharacteristic b M (nativeLine t) -
      finiteBracketCharacteristic c M (nativeLine t)) atTop
      (nhds ((factor b (nativeLine t) - factor c (nativeLine t)) *
        nativeScalar (nativeLine t))) := by
  have hd : nativeLine t ∈ bracketDomain := by simp [bracketDomain]; norm_num
  have hs : nativeLine t ∈ nativeScalarDomain := by simp [nativeScalarDomain]; norm_num
  have h := ((finiteBracketCharacteristic_tendstoLocallyUniformlyOn hb).tendsto_at hd).sub
    ((finiteBracketCharacteristic_tendstoLocallyUniformlyOn hc).tendsto_at hd)
  rw [bracketCharacteristic_eq_factor_mul_nativeScalar hb hs,
    bracketCharacteristic_eq_factor_mul_nativeScalar hc hs, ← sub_mul] at h
  exact h

end
end CarrySelfAdjointOperator
