import CarrySelfAdjointOperator.NativeGammaMixedProfiles

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped BigOperators InnerProductSpace ENNReal MeasureTheory
open Set MeasureTheory NativeCarrySpectralWeyl.Infinite
noncomputable section
set_option autoImplicit false

def nativeRealSixNaimarkSynthesis (c : Fin 6 → ℝ) : NaimarkSpace :=
  ∑ i, c i • naimarkCameraVector (atlasSixCameraIndex i)

theorem nativeRealSixNaimarkSynthesis_coeFn (c : Fin 6 → ℝ) :
    ⇑(nativeRealSixNaimarkSynthesis c) =ᵐ[positiveLebesgueMeasure]
      fun x => ∑ i, c i • nativeCameraFiber i x := by
  have hs (s : Finset (Fin 6)) :
      ⇑(∑ i ∈ s, c i • naimarkCameraVector (atlasSixCameraIndex i)) =ᵐ[positiveLebesgueMeasure]
        fun x => ∑ i ∈ s, c i • nativeCameraFiber i x := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact Lp.coeFn_zero (E := KolmogorovSpace) (p := 2) (μ := positiveLebesgueMeasure)
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (c i • naimarkCameraVector (atlasSixCameraIndex i))
          (∑ j ∈ s, c j • naimarkCameraVector (atlasSixCameraIndex j)),
        Lp.coeFn_smul (c i) (naimarkCameraVector (atlasSixCameraIndex i)),
        naimarkCameraVector_coeFn (atlasSixCameraIndex i), ih] with x ha hm hv hs
      simp only [ha, hm, hv, hs, Pi.add_apply, Pi.smul_apply]
      rfl
  exact hs Finset.univ

theorem nativeRealSixNaimarkSynthesis_mixed_coeFn :
    ⇑(nativeRealSixNaimarkSynthesis sixCameraMixedReturnRay) =ᵐ[positiveLebesgueMeasure]
      nativeMixedFiber := by
  have h := nativeRealSixNaimarkSynthesis_coeFn sixCameraMixedReturnRay
  filter_upwards [h] with x hx
  rw [hx]
  simp [sixCameraMixedReturnRay, Fin.sum_univ_succ, nativeMixedFiber, add_assoc]

theorem nativeMixed_multiplier_orthogonal (a b : BoundedRealNaimarkMultiplier)
    (c : Fin 6 → ℝ) (hc : c 4 = 0) :
    inner ℝ (boundedRealNaimarkMultiplier a (nativeRealSixNaimarkSynthesis sixCameraMixedReturnRay))
      (boundedRealNaimarkMultiplier b (nativeRealSixNaimarkSynthesis c)) = 0 := by
  rw [L2.inner_def]
  have he : (fun x => inner ℝ
      ((boundedRealNaimarkMultiplier a (nativeRealSixNaimarkSynthesis sixCameraMixedReturnRay)) x)
      ((boundedRealNaimarkMultiplier b (nativeRealSixNaimarkSynthesis c)) x)) =ᵐ[positiveLebesgueMeasure]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [boundedRealNaimarkMultiplier_coeFn a
        (nativeRealSixNaimarkSynthesis sixCameraMixedReturnRay),
      boundedRealNaimarkMultiplier_coeFn b (nativeRealSixNaimarkSynthesis c),
      nativeRealSixNaimarkSynthesis_mixed_coeFn,
      nativeRealSixNaimarkSynthesis_coeFn c] with x ha hb hm hc'
    rw [ha, hb, boundedRealNaimarkMultiplierFunction, boundedRealNaimarkMultiplierFunction,
      hm, hc', real_inner_smul_left, real_inner_smul_right,
      nativeMixedFiber_complement_inner c hc x, mul_zero, mul_zero]
  rw [integral_congr_ae he, integral_zero]

theorem nativeSixCameraSynthesis_naimark_re (c : Fin 6 → ℂ) :
    naimarkIsometry (RealHilbertComplexification.re (nativeSixCameraSynthesis c)) =
      nativeRealSixNaimarkSynthesis (fun i => (c i).re) := by
  simp [nativeSixCameraSynthesis, nativeComplexCameraVector,
    nativeRealSixNaimarkSynthesis, Fin.sum_univ_succ]

theorem nativeSixCameraSynthesis_naimark_im (c : Fin 6 → ℂ) :
    naimarkIsometry (RealHilbertComplexification.im (nativeSixCameraSynthesis c)) =
      nativeRealSixNaimarkSynthesis (fun i => (c i).im) := by
  simp [nativeSixCameraSynthesis, nativeComplexCameraVector,
    nativeRealSixNaimarkSynthesis, Fin.sum_univ_succ]

end
end CarrySelfAdjointOperator.GammaMaterialSewing
