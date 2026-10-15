import CarrySelfAdjointOperator.NativeCompletedSourcePositiveReductionJet

/-! Two positive source channels and the exact remaining native kernel.
The source controls both scales unconditionally. No sign is assigned to the
second reduced kernel. The formula works for every finite source family. -/
namespace CarrySelfAdjointOperator.SourcePositiveReduction
open DividedVectorResponse Filter
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def secondAxis (z : ℂ) : ℂ := dslope reducedResponse 0 z

theorem secondAxis_analyticAt_zero : AnalyticAt ℂ secondAxis 0 := by
  rcases reducedResponse_analyticAt_zero with ⟨p, hp⟩
  exact hp.has_fpower_series_dslope_fslope.analyticAt

theorem secondAxis_zero : secondAxis 0 = (reducedSourceScale : ℂ) := by
  rw [secondAxis, dslope_same, reducedSourceScale_eq,
    reducedResponse_hasDerivAt_zero.deriv]
  simp

theorem reducedResponse_eq_mul_secondAxis (z : ℂ) :
    reducedResponse z = z * secondAxis z := by
  have h := sub_smul_dslope reducedResponse 0 z
  simpa only [sub_zero, reducedResponse_zero, smul_eq_mul, secondAxis] using h.symm

/-- This response is defined by a second application of the SAME source
quotient operation, with its source-derived central scale. -/
def secondReducedResponse (z : ℂ) : ℂ :=
  dslope secondAxis 0 z / ((reducedSourceScale : ℂ)*secondAxis z)

theorem secondReducedResponse_source_equation (z : ℂ) (hz : secondAxis z ≠ 0) :
    reducedResponse z*secondReducedResponse z =
      secondAxis z/(reducedSourceScale : ℂ)-1 := by
  have ha : (reducedSourceScale : ℂ) ≠ 0 := by exact_mod_cast reducedSourceScale_pos.ne'
  have h := sub_smul_dslope secondAxis 0 z
  simp only [sub_zero, smul_eq_mul, secondAxis_zero] at h
  rw [reducedResponse_eq_mul_secondAxis, secondReducedResponse]
  field_simp
  linear_combination h

theorem secondReducedResponse_analyticAt_zero : AnalyticAt ℂ secondReducedResponse 0 := by
  rcases secondAxis_analyticAt_zero with ⟨p, hp⟩
  apply hp.has_fpower_series_dslope_fslope.analyticAt.div
    (analyticAt_const.mul secondAxis_analyticAt_zero)
  change (reducedSourceScale : ℂ)*secondAxis 0 ≠ 0
  rw [secondAxis_zero]
  exact mul_ne_zero (by exact_mod_cast reducedSourceScale_pos.ne')
    (by exact_mod_cast reducedSourceScale_pos.ne')

def secondPositiveFeature (z : ℂ) : ℂ :=
  secondAxis z/(Real.sqrt reducedSourceScale : ℂ)

theorem secondPositiveFeature_inner (z w : ℂ) :
    inner ℂ (secondPositiveFeature z) (secondPositiveFeature w) =
      conj (secondAxis z)*secondAxis w/(reducedSourceScale : ℂ) := by
  have hsq : (Real.sqrt reducedSourceScale : ℂ)^2 = (reducedSourceScale : ℂ) := by
    exact_mod_cast Real.sq_sqrt reducedSourceScale_pos.le
  simp only [secondPositiveFeature, RCLike.inner_apply, map_div₀, Complex.conj_ofReal]
  rw [div_mul_div_comm]
  rw [mul_comm (secondAxis w), ← pow_two, hsq]

theorem secondPositiveFeature_zero :
    secondPositiveFeature 0 = (Real.sqrt reducedSourceScale : ℂ) := by
  rw [secondPositiveFeature, secondAxis_zero]
  have hs : (Real.sqrt reducedSourceScale : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr reducedSourceScale_pos).ne'
  have hsq : (Real.sqrt reducedSourceScale : ℂ)^2 = (reducedSourceScale : ℂ) := by
    exact_mod_cast Real.sq_sqrt reducedSourceScale_pos.le
  rw [← hsq]
  field_simp

theorem secondChannel_hasDerivAt_zero :
    HasDerivAt (sourceResponse * secondPositiveFeature)
      ((sourceScale : ℂ)*(Real.sqrt reducedSourceScale : ℂ)) 0 := by
  have hr := sourceResponse_analyticAt_zero.differentiableAt.hasDerivAt
  have hder : deriv sourceResponse 0 = (sourceScale : ℂ) := by
    rw [← dslope_same, ← sourceAxis_eq_dslope, sourceAxis_zero_eq_scale]
  rw [hder] at hr
  have hs : (Real.sqrt reducedSourceScale : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr reducedSourceScale_pos).ne'
  have hf : AnalyticAt ℂ secondPositiveFeature 0 :=
    secondAxis_analyticAt_zero.div analyticAt_const hs
  have h := hr.mul hf.differentiableAt.hasDerivAt
  simpa only [secondPositiveFeature_zero, sourceResponse_zero, zero_mul, add_zero] using h

theorem secondChannel_firstJet_energy :
    ‖deriv (sourceResponse * secondPositiveFeature) 0‖^2 =
      canonicalCompletedNativeLogDerivativeMoment 1 := by
  rw [secondChannel_hasDerivAt_zero.deriv]
  have he : (sourceScale : ℂ)*(Real.sqrt reducedSourceScale : ℂ) =
      ((sourceScale*Real.sqrt reducedSourceScale : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt reducedSourceScale_pos.le, reducedSourceScale_eq]
  field_simp [sourceScale_pos.ne']

def secondReducedKernel (z w : ℂ) : ℂ :=
  (secondReducedResponse w-conj (secondReducedResponse z))/(w-conj z)

theorem reducedKernel_split (z w : ℂ)
    (hz : secondAxis z ≠ 0) (hw : secondAxis w ≠ 0) (hsep : w ≠ conj z) :
    reducedKernel z w = inner ℂ (secondPositiveFeature z) (secondPositiveFeature w) +
      conj (reducedResponse z)*reducedResponse w*secondReducedKernel z w := by
  have hzw := secondReducedResponse_source_equation w hw
  have hzz := congrArg conj (secondReducedResponse_source_equation z hz)
  simp only [map_mul, map_sub, map_div₀, map_one, Complex.conj_ofReal] at hzz
  have hnum : reducedResponse w-conj (reducedResponse z) =
      (w-conj z)*inner ℂ (secondPositiveFeature z) (secondPositiveFeature w) +
      conj (reducedResponse z)*reducedResponse w*
        (secondReducedResponse w-conj (secondReducedResponse z)) := by
    rw [secondPositiveFeature_inner, reducedResponse_eq_mul_secondAxis w,
      reducedResponse_eq_mul_secondAxis z, map_mul] at *
    linear_combination -(conj z*conj (secondAxis z))*hzw + (w*secondAxis w)*hzz
  unfold reducedKernel secondReducedKernel
  rw [hnum]
  field_simp [sub_ne_zero.mpr hsep]

/-- A fixed two-channel Hilbert space. Its second coordinate includes the
original source response; it is not a separately fitted moment column. -/
def positivePair (z : ℂ) : WithLp 2 (ℂ × ℂ) :=
  WithLp.toLp 2 (positiveFeature z, sourceResponse z*secondPositiveFeature z)

def residualAmplitude (z : ℂ) : ℂ := sourceResponse z*reducedResponse z

/-- The complete residual has a quadratic zero in each polarized leg.
This is an exact factor, not a dropped Taylor tail. -/
theorem residualAmplitude_quadratic (z : ℂ) :
    residualAmplitude z = z^2*(sourceAxis z*secondAxis z) := by
  rw [residualAmplitude, sourceResponse_eq_mul_axis, reducedResponse_eq_mul_secondAxis]
  ring

theorem positivePair_inner (z w : ℂ) :
    inner ℂ (positivePair z) (positivePair w) =
      inner ℂ (positiveFeature z) (positiveFeature w) +
        conj (sourceResponse z)*sourceResponse w*
          inner ℂ (secondPositiveFeature z) (secondPositiveFeature w) := by
  rw [WithLp.prod_inner_apply]
  simp only [positivePair, WithLp.ofLp_toLp, RCLike.inner_apply, map_mul]
  ring

/-- The original source kernel, with two positive channels AND the entire
remaining source response. Neither the sign nor vanishing of the latter
is claimed. All two-input terms retain their original weights. -/
theorem sourceKernel_two_positive_channels (z w : ℂ)
    (haz : sourceAxis z ≠ 0) (haw : sourceAxis w ≠ 0)
    (hbz : secondAxis z ≠ 0) (hbw : secondAxis w ≠ 0) (hsep : w ≠ conj z) :
    sourceKernel z w = inner ℂ (positivePair z) (positivePair w) +
      conj (residualAmplitude z)*residualAmplitude w*secondReducedKernel z w := by
  rw [sourceKernel_split z w haz haw hsep, reducedKernel_split z w hbz hbw hsep,
    positivePair_inner]
  simp only [residualAmplitude, map_mul]
  ring

theorem positivePair_center_energy :
    ‖positivePair 0‖^2 = canonicalCompletedNativeLogDerivativeMoment 0 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖positiveFeature 0‖^2 + ‖sourceResponse 0*secondPositiveFeature 0‖^2 = _
  simp only [sourceResponse_zero, zero_mul, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
  rw [positiveFeature_center_energy, sourceScale_eq]

private theorem finite_gram_energy {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {N : ℕ} (c : Fin N → ℂ) (v : Fin N → H) :
    ∑ i, ∑ j, conj (c i)*c j*inner ℂ (v i) (v j) =
      ((‖∑ i, c i • v i‖^2 : ℝ) : ℂ) := by
  calc
    _ = inner ℂ (∑ i, c i • v i) (∑ i, c i • v i) := by
      simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      apply Complex.ext
      · exact inner_self_eq_norm_sq (𝕜 := ℂ) _
      · exact inner_self_im (𝕜 := ℂ) _

/-- Every finite dimension, two independent source slots, all crossings.
The positive term is a literal norm in one fixed Hilbert carrier. -/
theorem sourceKernel_two_channel_finite_energy {N : ℕ} (c : Fin N → ℂ) (z : Fin N → ℂ)
    (ha : ∀ i, sourceAxis (z i) ≠ 0) (hb : ∀ i, secondAxis (z i) ≠ 0)
    (hsep : ∀ i j, z j ≠ conj (z i)) :
    ∑ i, ∑ j, conj (c i)*c j*sourceKernel (z i) (z j) =
      ((‖∑ i, c i • positivePair (z i)‖^2 : ℝ) : ℂ) +
        ∑ i, ∑ j, conj (c i*residualAmplitude (z i))*(c j*residualAmplitude (z j))*
          secondReducedKernel (z i) (z j) := by
  rw [← finite_gram_energy]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [sourceKernel_two_positive_channels _ _ (ha i) (ha j) (hb i) (hb j) (hsep i j), map_mul]
  ring

/-- On combinations cancelling the positive pair, the entire energy is
the retained source residual. This prevents a rank-two prefix from being
misreported as all-order positivity. -/
theorem sourceKernel_energy_on_positive_nullspace {N : ℕ}
    (c : Fin N → ℂ) (z : Fin N → ℂ)
    (ha : ∀ i, sourceAxis (z i) ≠ 0) (hb : ∀ i, secondAxis (z i) ≠ 0)
    (hsep : ∀ i j, z j ≠ conj (z i))
    (hcancel : ∑ i, c i • positivePair (z i) = 0) :
    ∑ i, ∑ j, conj (c i)*c j*sourceKernel (z i) (z j) =
      ∑ i, ∑ j, conj (c i*residualAmplitude (z i))*(c j*residualAmplitude (z j))*
        secondReducedKernel (z i) (z j) := by
  rw [sourceKernel_two_channel_finite_energy c z ha hb hsep, hcancel]
  simp

/-- The neighborhood and both nonzero axes are supplied unconditionally by
the source. The native response is -F'/(2F), with its original completion. -/
theorem nativeKernel_two_positive_channels_local :
    ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧
      ∀ z ∈ U, ∀ w ∈ U, w ≠ conj z →
        (completedGreenNormalizedResponse completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion w -
          conj (completedGreenNormalizedResponse completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion z))/(w-conj z) =
          inner ℂ (positivePair z) (positivePair w) +
            conj (residualAmplitude z)*residualAmplitude w*secondReducedKernel z w := by
  rcases sourceKernel_eq_native_local with ⟨V, hV, hzero, hkernel⟩
  have hb : ∀ᶠ z : ℂ in nhds 0, secondAxis z ≠ 0 := by
    apply secondAxis_analyticAt_zero.continuousAt.eventually_ne
    rw [secondAxis_zero]
    exact_mod_cast reducedSourceScale_pos.ne'
  rcases mem_nhds_iff.mp hb with ⟨W, hW, hopen, hWzero⟩
  refine ⟨V ∩ W, hV.inter hopen, ⟨hzero, hWzero⟩, ?_⟩
  intro z hz w hw hsep
  have hh := hkernel z hz.1 w hw.1
  rw [← hh.2.2]
  exact sourceKernel_two_positive_channels z w hh.1 hh.2.1 (hW hz.2) (hW hw.2) hsep

end
end CarrySelfAdjointOperator.SourcePositiveReduction
