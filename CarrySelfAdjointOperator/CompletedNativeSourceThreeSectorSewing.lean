import CarrySelfAdjointOperator.NativeGammaNaimarkHaloEscape
import CarrySelfAdjointOperator.CompletedNativeChiralReturnGammaCorrectionCancellation

/-!
# Three sectors of the same completed source

The existing six-camera projection, coherent exterior and global Naimark
escape are applied after full source synthesis. All ordered crosses survive.
The completed ambient response has zero global escape; its resolved source
correction cancels the Gamma escape, rather than creating a new free positive
channel. The final identities retain the original signed Wronskian balance.
-/
namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped BigOperators InnerProductSpace ComplexConjugate
open CPFormal.Analytic.Cp
noncomputable section
set_option autoImplicit false

/-- Six-camera part, in the original camera metric. -/
def nativeNaimarkObserved : CarryGammaComplexNaimark →ₗ[ℂ] CarryGammaComplexCamera :=
  nativeSixCameraProjection.comp nativeComplexNaimarkAdjoint

/-- Coherent exterior to the six-camera atlas, still in the global camera Hilbert. -/
def nativeNaimarkHalo : CarryGammaComplexNaimark →ₗ[ℂ] CarryGammaComplexCamera :=
  nativeSixCameraExterior.comp nativeComplexNaimarkAdjoint

theorem nativeNaimarkGlobal_roundtrip (x : CarryGammaComplexNaimark) :
    x = nativeComplexNaimarkPort (nativeComplexNaimarkAdjoint x) +
      nativeComplexGlobalNaimarkEscape x := by
  change x = nativeComplexNaimarkPort (nativeComplexNaimarkAdjoint x) +
    (x - nativeComplexNaimarkPort (nativeComplexNaimarkAdjoint x))
  abel

theorem nativeNaimarkGlobalEscape_port (u : CarryGammaComplexCamera) :
    nativeComplexGlobalNaimarkEscape (nativeComplexNaimarkPort u) = 0 := by
  change nativeComplexNaimarkPort u - nativeComplexNaimarkPort
    (nativeComplexNaimarkAdjoint (nativeComplexNaimarkPort u)) = 0
  rw [nativeComplexNaimarkAdjoint_port, sub_self]

theorem nativeNaimarkGlobalEscape_orthogonal (u : CarryGammaComplexCamera)
    (x : CarryGammaComplexNaimark) :
    inner ℂ (nativeComplexNaimarkPort u) (nativeComplexGlobalNaimarkEscape x) = 0 := by
  change inner ℂ (nativeComplexNaimarkPort u)
    (x - nativeComplexNaimarkPort (nativeComplexNaimarkAdjoint x)) = 0
  rw [inner_sub_right, nativeComplexNaimark_adjoint_inner,
    nativeComplexNaimarkPort_inner, sub_self]

/-- Polarization for arbitrary ambient vectors, not only individual Gamma nodes. -/
theorem nativeNaimarkThreeSector_inner (x y : CarryGammaComplexNaimark) :
    inner ℂ x y =
      inner ℂ (nativeNaimarkObserved x) (nativeNaimarkObserved y) +
      inner ℂ (nativeNaimarkHalo x) (nativeNaimarkHalo y) +
      inner ℂ (nativeComplexGlobalNaimarkEscape x) (nativeComplexGlobalNaimarkEscape y) := by
  have hreverse (u : CarryGammaComplexCamera) (v : CarryGammaComplexNaimark) :
      inner ℂ (nativeComplexGlobalNaimarkEscape v) (nativeComplexNaimarkPort u) = 0 := by
    rw [← inner_conj_symm, nativeNaimarkGlobalEscape_orthogonal, map_zero]
  have hcamera :
      inner ℂ (nativeComplexNaimarkAdjoint x) (nativeComplexNaimarkAdjoint y) =
        inner ℂ (nativeNaimarkObserved x) (nativeNaimarkObserved y) +
          inner ℂ (nativeNaimarkHalo x) (nativeNaimarkHalo y) := by
    change inner ℂ _ _ =
      inner ℂ (nativeSixCameraSynthesis (nativeSixCameraCoordinates _))
        (nativeSixCameraSynthesis (nativeSixCameraCoordinates _)) + _
    rw [nativeSixCameraSynthesis_inner]
    exact nativeSixCameraProjection_metricLedger _ _
  calc
    inner ℂ x y = inner ℂ
        (nativeComplexNaimarkPort (nativeComplexNaimarkAdjoint x) +
          nativeComplexGlobalNaimarkEscape x)
        (nativeComplexNaimarkPort (nativeComplexNaimarkAdjoint y) +
          nativeComplexGlobalNaimarkEscape y) := by
      rw [← nativeNaimarkGlobal_roundtrip, ← nativeNaimarkGlobal_roundtrip]
    _ = inner ℂ (nativeComplexNaimarkAdjoint x) (nativeComplexNaimarkAdjoint y) +
        inner ℂ (nativeComplexGlobalNaimarkEscape x) (nativeComplexGlobalNaimarkEscape y) := by
      simp only [inner_add_left, inner_add_right, nativeComplexNaimarkPort_inner,
        nativeNaimarkGlobalEscape_orthogonal, hreverse, add_zero, zero_add]
    _ = _ := by rw [hcamera]

theorem nativeNaimarkThreeSector_norm_sq (x : CarryGammaComplexNaimark) :
    ‖x‖ ^ 2 = ‖nativeNaimarkObserved x‖ ^ 2 + ‖nativeNaimarkHalo x‖ ^ 2 +
      ‖nativeComplexGlobalNaimarkEscape x‖ ^ 2 := by
  have h := congrArg Complex.re (nativeNaimarkThreeSector_inner x x)
  have hreal (a : ℝ) : ((a : ℂ) ^ 2).re = a ^ 2 := by
    rw [← Complex.ofReal_pow]
    rfl
  simp only [Complex.add_re, inner_self_eq_norm_sq_to_K] at h
  change ((‖x‖ : ℂ) ^ 2).re =
    ((‖nativeNaimarkObserved x‖ : ℂ) ^ 2).re +
      ((‖nativeNaimarkHalo x‖ : ℂ) ^ 2).re +
      ((‖nativeComplexGlobalNaimarkEscape x‖ : ℂ) ^ 2).re at h
  simpa only [hreal] using h

theorem nativeCameraTwoSector_norm_sq (u : CarryGammaComplexCamera) :
    ‖u‖ ^ 2 = ‖nativeSixCameraProjection u‖ ^ 2 +
      ‖nativeSixCameraExterior u‖ ^ 2 := by
  have h := nativeNaimarkThreeSector_norm_sq (nativeComplexNaimarkPort u)
  simpa [nativeNaimarkObserved, nativeNaimarkHalo, nativeComplexNaimarkAdjoint_port,
    nativeNaimarkGlobalEscape_port, nativeComplexNaimarkPort_norm] using h

/-- The actual completed ambient response occupies the ordinary global port. -/
theorem nativeCompletedAmbientResponse_eq_port (z : ℂ)
    (hs : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3AmbientResponseState z hs =
      nativeComplexNaimarkPort (canonicalCompletedC3GammaCameraView
        (completedC3SymplecticCameraState (operatorHeightParameter z) hs)) := by
  rw [nativeComplexNaimarkPort_eq_original]
  rfl

theorem nativeCompletedAmbientResponse_globalEscape_zero (z : ℂ)
    (hs : 0 < (operatorHeightParameter z).re) :
    nativeComplexGlobalNaimarkEscape (canonicalCompletedC3AmbientResponseState z hs) = 0 := by
  rw [nativeCompletedAmbientResponse_eq_port, nativeNaimarkGlobalEscape_port]

/-- Exact cancellation on the source-defined resolved correction. -/
theorem nativeCompletedResolvedCorrection_globalEscape (z : ℂ) (hz : z.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re) :
    nativeComplexGlobalNaimarkEscape
        (canonicalCompletedC3AmbientTfvdResolvedCorrectionState z hz hs) =
      -nativeComplexGlobalNaimarkEscape (canonicalCompletedC3PolarizedGammaState z hz) := by
  have h := congrArg nativeComplexGlobalNaimarkEscape
    (canonicalCompletedC3AmbientResponseState_eq_gamma_add_correction z hz hs)
  rw [nativeCompletedAmbientResponse_globalEscape_zero, map_add] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- Cancellation includes both ordered crosses on independent source parameters. -/
theorem nativeCompletedGlobalEscape_fourTerms_zero (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re)
    (ht : 0 < (operatorHeightParameter w).re) :
    let g := fun q hq => nativeComplexGlobalNaimarkEscape
      (canonicalCompletedC3PolarizedGammaState q hq)
    let d := fun q hq hhalf => nativeComplexGlobalNaimarkEscape
      (canonicalCompletedC3AmbientTfvdResolvedCorrectionState q hq hhalf)
    inner ℂ (g z hz) (g w hw) + inner ℂ (g z hz) (d w hw ht) +
      inner ℂ (d z hz hs) (g w hw) + inner ℂ (d z hz hs) (d w hw ht) = 0 := by
  dsimp only
  simp only [nativeCompletedResolvedCorrection_globalEscape, inner_neg_left, inner_neg_right]
  abel

/-- Polarized two-sector ledger for the actual completed ambient response. -/
theorem nativeCompletedAmbientResponse_twoSector_inner (z w : ℂ)
    (hs : 0 < (operatorHeightParameter z).re)
    (ht : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3AmbientResponseKernel z w hs ht =
      inner ℂ (nativeNaimarkObserved (canonicalCompletedC3AmbientResponseState z hs))
        (nativeNaimarkObserved (canonicalCompletedC3AmbientResponseState w ht)) +
      inner ℂ (nativeNaimarkHalo (canonicalCompletedC3AmbientResponseState z hs))
        (nativeNaimarkHalo (canonicalCompletedC3AmbientResponseState w ht)) := by
  unfold canonicalCompletedC3AmbientResponseKernel
  rw [nativeNaimarkThreeSector_inner,
    nativeCompletedAmbientResponse_globalEscape_zero,
    nativeCompletedAmbientResponse_globalEscape_zero, inner_zero_left, add_zero]

/-- Direct comparison with the original completed (F,-F') Wronskian.
The separation and all four existing correction channels are unchanged. -/
theorem nativeCompletedWronskianDefect_eq_twoSectorBoundary (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip)
    (ht : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3CoisometricWronskianFourChannelDefect z w hz hw hs.1 ht.1 =
      (w - conj z) *
        (inner ℂ (nativeNaimarkObserved (canonicalCompletedC3AmbientResponseState z hs.1))
            (nativeNaimarkObserved (canonicalCompletedC3AmbientResponseState w ht.1)) +
          inner ℂ (nativeNaimarkHalo (canonicalCompletedC3AmbientResponseState z hs.1))
            (nativeNaimarkHalo (canonicalCompletedC3AmbientResponseState w ht.1))) -
        completedGreenWronskian completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion w z := by
  rw [canonicalCompletedC3CoisometricWronskianFourChannelDefect_eq_sub z w hz hw hs ht,
    canonicalCompletedC3CoisometricCompressedBoundaryReadout_eq_kernel,
    inner_completedC3SymplecticCameraState_eq_ambientResponseKernel,
    nativeCompletedAmbientResponse_twoSector_inner]

end
end CarrySelfAdjointOperator.GammaMaterialSewing

namespace CarrySelfAdjointOperator.ChiralReturn
open scoped BigOperators InnerProductSpace ComplexConjugate
open CPFormal.Analytic.Cp GammaMaterialSewing
noncomputable section
set_option autoImplicit false

/-- The source coefficients are synthesized BEFORE any of the three projections. -/
theorem polarizedSourceBalance_eq_threeSectorGamma_add_rawBalance
    (M k : ℕ) {N : ℕ} (c d : Fin N → ℂ) (r s : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip) :
    polarizedSourceBalance k c d r s =
      2 * (inner ℂ (nativeNaimarkObserved (gammaSourceSynthesis k c r))
              (nativeNaimarkObserved (gammaSourceSynthesis k d s)) +
        inner ℂ (nativeNaimarkHalo (gammaSourceSynthesis k c r))
          (nativeNaimarkHalo (gammaSourceSynthesis k d s)) +
        inner ℂ (nativeComplexGlobalNaimarkEscape (gammaSourceSynthesis k c r))
          (nativeComplexGlobalNaimarkEscape (gammaSourceSynthesis k d s))) +
      2 * Complex.I * rawGammaWronskianBalance k c d r s := by
  rw [polarizedSourceBalance_eq_gammaGram_add_rawGammaBalance M k c d r s hstrip,
    nativeNaimarkThreeSector_inner]

/-- The original storage, same source and weights, at arbitrary finite order. -/
theorem storage_re_eq_threeSectorGammaBudget
    (M k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (hpositive : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (storage k c r).re =
      2 * (‖nativeNaimarkObserved (gammaSourceSynthesis k c r)‖ ^ 2 +
        ‖nativeNaimarkHalo (gammaSourceSynthesis k c r)‖ ^ 2 +
        ‖nativeComplexGlobalNaimarkEscape (gammaSourceSynthesis k c r)‖ ^ 2) -
      2 * (rawGammaWronskianBalance k c c r r).im := by
  rw [storage_re_eq_gammaEnergy_sub_rawGammaBalance M k c r hstrip hpositive,
    nativeNaimarkThreeSector_norm_sq]

theorem storage_nonnegative_iff_threeSectorGammaBudget
    (M k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (hpositive : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    0 ≤ (storage k c r).re ↔
      (rawGammaWronskianBalance k c c r r).im ≤
        ‖nativeNaimarkObserved (gammaSourceSynthesis k c r)‖ ^ 2 +
        ‖nativeNaimarkHalo (gammaSourceSynthesis k c r)‖ ^ 2 +
        ‖nativeComplexGlobalNaimarkEscape (gammaSourceSynthesis k c r)‖ ^ 2 := by
  rw [storage_re_eq_threeSectorGammaBudget M k c r hstrip hpositive]
  constructor <;> intro h <;> linarith

/-- The global-escape Gram is present in the signed correction with its exact
coefficient, including both independently synthesized source arguments. -/
theorem rawGammaBalance_sub_globalEscapeGram
    (k : ℕ) {N : ℕ} (c d : Fin N → ℂ) (r s : ℝ)
    (hhalf : ∀ i : Fin N, 0 < (operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i)).re) :
    rawGammaWronskianBalance k c d r s - Complex.I *
        inner ℂ (nativeComplexGlobalNaimarkEscape (gammaSourceSynthesis k c r))
          (nativeComplexGlobalNaimarkEscape (gammaSourceSynthesis k d s)) =
      coisometricFourChannelBalance k c d r s hhalf + Complex.I *
        (inner ℂ (nativeNaimarkObserved (gammaSourceSynthesis k c r))
            (nativeNaimarkObserved (gammaSourceSynthesis k d s)) +
          inner ℂ (nativeNaimarkHalo (gammaSourceSynthesis k c r))
            (nativeNaimarkHalo (gammaSourceSynthesis k d s)) -
          inner ℂ (coisometricSourceSynthesis k c r hhalf)
            (coisometricSourceSynthesis k d s hhalf)) := by
  rw [coisometricFourChannelBalance_eq_rawGamma_add_gram_difference,
    nativeNaimarkThreeSector_inner (gammaSourceSynthesis k c r) (gammaSourceSynthesis k d s)]
  ring

/-- The global-escape energy is also present in the signed correction.
Subtracting it exposes the SAME original coisometric comparison, with no
unconditional sign asserted and no additional positive margin manufactured. -/
theorem rawGammaBalance_sub_globalEscape_eq_coisometricBudget
    (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ)
    (hhalf : ∀ i : Fin N, 0 < (operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i)).re) :
    (rawGammaWronskianBalance k c c r r).im -
        ‖nativeComplexGlobalNaimarkEscape (gammaSourceSynthesis k c r)‖ ^ 2 =
      (coisometricFourChannelBalance k c c r r hhalf).im +
        ‖nativeNaimarkObserved (gammaSourceSynthesis k c r)‖ ^ 2 +
        ‖nativeNaimarkHalo (gammaSourceSynthesis k c r)‖ ^ 2 -
        ‖coisometricSourceSynthesis k c r hhalf‖ ^ 2 := by
  have h := congrArg Complex.im
    (coisometricFourChannelBalance_eq_rawGamma_add_gram_difference k c c r r hhalf)
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have hreal (a : ℝ) : ((a : ℂ) ^ 2).re = a ^ 2 := by
    rw [← Complex.ofReal_pow]
    rfl
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_add, Complex.sub_re] at h
  change (coisometricFourChannelBalance k c c r r hhalf).im =
    (rawGammaWronskianBalance k c c r r).im +
      (((‖coisometricSourceSynthesis k c r hhalf‖ : ℂ) ^ 2).re -
        ((‖gammaSourceSynthesis k c r‖ : ℂ) ^ 2).re) at h
  rw [hreal, hreal] at h
  have he := nativeNaimarkThreeSector_norm_sq (gammaSourceSynthesis k c r)
  linarith

/-- Completed-camera form of the same budget: only the six-camera sector and
coherent halo remain, and the four-channel correction is retained unchanged. -/
theorem storage_re_eq_completedCameraTwoSectorBudget
    (M k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (hpositive : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (storage k c r).re =
      2 * (‖nativeSixCameraProjection
            (coisometricSourceSynthesis k c r (fun i => (hstrip i).1))‖ ^ 2 +
        ‖nativeSixCameraExterior
            (coisometricSourceSynthesis k c r (fun i => (hstrip i).1))‖ ^ 2) -
      2 * (coisometricFourChannelBalance k c c r r (fun i => (hstrip i).1)).im := by
  rw [storage_re_eq_coisometricEnergy_sub_fourChannelBalance M k c r hstrip hpositive,
    nativeCameraTwoSector_norm_sq]

/-- Source regularity supplies a threshold for each finite order, uniform in
all coefficients and internal radii. No uniform threshold in N or sign claim. -/
theorem threeSectorGammaBudget_eventually (N : ℕ) :
    ∀ᶠ k : ℕ in Filter.atTop, ∀ c : Fin N → ℂ, ∀ r : ℝ,
      (storage k c r).re =
        2 * (‖nativeNaimarkObserved (gammaSourceSynthesis k c r)‖ ^ 2 +
          ‖nativeNaimarkHalo (gammaSourceSynthesis k c r)‖ ^ 2 +
          ‖nativeComplexGlobalNaimarkEscape (gammaSourceSynthesis k c r)‖ ^ 2) -
        2 * (rawGammaWronskianBalance k c c r r).im := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N]
    with k hreg
  intro c r
  exact storage_re_eq_threeSectorGammaBudget 0 k c r
    (fun i => (hreg i).1) (fun i => (hreg i).2.2)

end
end CarrySelfAdjointOperator.ChiralReturn
