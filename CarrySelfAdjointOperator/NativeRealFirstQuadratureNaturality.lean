import CarrySelfAdjointOperator.RealQuadratureDomainTransport
import CarrySelfAdjointOperator.CompletedNativeSourceThreeSectorSewing

/-! Faithful posterior complex packaging of the real quadrature construction.
The complete metric AND rotation-associated form survive. The native Green
defect is transported as two real equations; it is not set to zero. -/
namespace CarrySelfAdjointOperator.RealQuadrature
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def pack (x : Space E) : RealHilbertComplexification E :=
  RealHilbertComplexification.mk x.fst x.snd

def unpack (x : RealHilbertComplexification E) : Space E :=
  WithLp.toLp 2 (RealHilbertComplexification.re x, RealHilbertComplexification.im x)

omit [InnerProductSpace ℝ E] in
@[simp] theorem pack_unpack (x : RealHilbertComplexification E) : pack (unpack x) = x := rfl
omit [InnerProductSpace ℝ E] in
@[simp] theorem unpack_pack (x : Space E) : unpack (pack x) = x := rfl
omit [InnerProductSpace ℝ E] in
theorem pack_norm (x : Space E) : ‖pack x‖ = ‖x‖ := rfl

/-- Reconstructs BOTH polarized components on independent real source vectors. -/
theorem pack_inner (x y : Space E) :
    inner ℂ (pack x) (pack y) =
      (inner ℝ x y : ℂ) + Complex.I * (inner ℝ (J x) y : ℂ) := by
  change RealHilbertComplexification.complexInner (pack x) (pack y) = _
  simp only [RealHilbertComplexification.complexInner, pack,
    RealHilbertComplexification.re_mk, RealHilbertComplexification.im_mk]
  change ((inner ℝ x.fst y.fst + inner ℝ x.snd y.snd : ℝ) : ℂ) +
    Complex.I * ((inner ℝ x.fst y.snd - inner ℝ x.snd y.fst : ℝ) : ℂ) =
    ((inner ℝ x.fst y.fst + inner ℝ x.snd y.snd : ℝ) : ℂ) +
    Complex.I * ((inner ℝ (-x.snd) y.fst + inner ℝ x.fst y.snd : ℝ) : ℂ)
  rw [inner_neg_left]
  congr 2
  ring

theorem pack_J (x : Space E) : pack (J x) = Complex.I • pack x := by
  apply RealHilbertComplexification.ext <;>
    simp [pack, RealHilbertComplexification.re_smul, RealHilbertComplexification.im_smul]

/-- The extra condition on a real isometry of doubled carriers is explicit. -/
theorem pack_inner_of_rotation_intertwining
    (L : Space E →ₗᵢ[ℝ] Space F) (hJ : ∀ x, L (J x) = J (L x))
    (x y : Space E) :
    inner ℂ (pack (L x)) (pack (L y)) = inner ℂ (pack x) (pack y) := by
  rw [pack_inner, pack_inner, ← hJ, L.inner_map_map, L.inner_map_map]

/-- Literal comparison with the already existing complexification of real maps. -/
theorem pack_lift (T : E →L[ℝ] F) (x : Space E) :
    pack (lift T.toLinearMap x) =
      GammaMaterialSewing.nativeComplexificationMap T (pack x) := rfl

theorem pack_double_domain_iff (T : E →ₗ.[ℝ] F) (x : Space E) :
    x ∈ (double T).domain ↔ pack x ∈ T.complexification.domain := Iff.rfl

/-- The previously constructed complex operator is the packaging of the REAL
doubled operator, on exactly its domain. -/
theorem pack_double_action (T : E →ₗ.[ℝ] F) (x : (double T).domain) :
    pack (double T x) = T.complexification
      ⟨pack (x : Space E), (pack_double_domain_iff T x).1 x.property⟩ := rfl

end
end CarrySelfAdjointOperator.RealQuadrature

namespace CarrySelfAdjointOperator.RealFirstNative
open scoped InnerProductSpace ComplexConjugate
open NativeCarrySpectralWeyl.Infinite CPFormal.Analytic.Cp RealQuadrature GammaMaterialSewing
noncomputable section
set_option autoImplicit false

/-- The three real operators already precede their complex packaging. -/
theorem realNaimarkThreeSector_inner (x y : NaimarkSpace) :
    inner ℝ x y =
      inner ℝ (sixCameraWhitenedNaimarkProjectionCLM x) (sixCameraWhitenedNaimarkProjectionCLM y) +
      inner ℝ (sixCameraGlobalCoherentHaloProjectionCLM x) (sixCameraGlobalCoherentHaloProjectionCLM y) +
      inner ℝ (globalNaimarkCameraEscape x) (globalNaimarkCameraEscape y) := by
  have he := sixCameraEscape_inner_eq_globalHalo_add_globalEscape x y
  have hp := sixCameraWhitenedNaimarkProjection_isSymmetric x y
  have hpp := sixCameraWhitenedNaimarkProjection_isSymmetric
    x (sixCameraWhitenedNaimarkProjection y)
  rw [sixCameraWhitenedNaimarkProjection_idempotent] at hpp
  change inner ℝ (x - sixCameraWhitenedNaimarkProjection x)
      (y - sixCameraWhitenedNaimarkProjection y) = _ at he
  simp only [inner_sub_left, inner_sub_right] at he
  simp only [sixCameraWhitenedNaimarkProjectionCLM_apply,
    sixCameraGlobalCoherentHaloProjectionCLM_apply]
  linarith

def observed : Space NaimarkSpace →ₗ[ℝ] Space NaimarkSpace :=
  lift sixCameraWhitenedNaimarkProjectionCLM.toLinearMap
def halo : Space NaimarkSpace →ₗ[ℝ] Space NaimarkSpace :=
  lift sixCameraGlobalCoherentHaloProjectionCLM.toLinearMap
def escape : Space NaimarkSpace →ₗ[ℝ] Space NaimarkSpace :=
  lift globalNaimarkCameraEscape.toLinearMap

theorem quadratureThreeSector_metric (x y : Space NaimarkSpace) :
    inner ℝ x y = inner ℝ (observed x) (observed y) +
      inner ℝ (halo x) (halo y) + inner ℝ (escape x) (escape y) := by
  have h1 := realNaimarkThreeSector_inner x.fst y.fst
  have h2 := realNaimarkThreeSector_inner x.snd y.snd
  change inner ℝ x.fst y.fst + inner ℝ x.snd y.snd =
    (inner ℝ (sixCameraWhitenedNaimarkProjectionCLM x.fst)
      (sixCameraWhitenedNaimarkProjectionCLM y.fst) +
      inner ℝ (sixCameraWhitenedNaimarkProjectionCLM x.snd)
        (sixCameraWhitenedNaimarkProjectionCLM y.snd)) +
    (inner ℝ (sixCameraGlobalCoherentHaloProjectionCLM x.fst)
      (sixCameraGlobalCoherentHaloProjectionCLM y.fst) +
      inner ℝ (sixCameraGlobalCoherentHaloProjectionCLM x.snd)
        (sixCameraGlobalCoherentHaloProjectionCLM y.snd)) +
    (inner ℝ (globalNaimarkCameraEscape x.fst) (globalNaimarkCameraEscape y.fst) +
      inner ℝ (globalNaimarkCameraEscape x.snd) (globalNaimarkCameraEscape y.snd))
  linarith

/-- The second polarized form is transported as well; the metric alone would
only recover the real part of the native identity. -/
theorem quadratureThreeSector_rotationForm (x y : Space NaimarkSpace) :
    inner ℝ (J x) y = inner ℝ (J (observed x)) (observed y) +
      inner ℝ (J (halo x)) (halo y) + inner ℝ (J (escape x)) (escape y) := by
  have h := quadratureThreeSector_metric (J x) y
  simpa only [observed, halo, escape, lift_J] using h

theorem quadratureThreeSector_pack_inner (x y : Space NaimarkSpace) :
    inner ℂ (pack x) (pack y) =
      inner ℂ (pack (observed x)) (pack (observed y)) +
      inner ℂ (pack (halo x)) (pack (halo y)) +
      inner ℂ (pack (escape x)) (pack (escape y)) := by
  simp only [pack_inner]
  rw [quadratureThreeSector_metric x y, quadratureThreeSector_rotationForm x y]
  push_cast
  ring

/-- Literal equality with the FULL polarized identity of PR 105. This compares
the complete sum; individual six-camera coordinate formulas are not asserted. -/
theorem pr105_full_pairing_comparison (x y : Space NaimarkSpace) :
    inner ℂ (nativeNaimarkObserved (pack x)) (nativeNaimarkObserved (pack y)) +
      inner ℂ (nativeNaimarkHalo (pack x)) (nativeNaimarkHalo (pack y)) +
      inner ℂ (nativeComplexGlobalNaimarkEscape (pack x))
        (nativeComplexGlobalNaimarkEscape (pack y)) =
      inner ℂ (pack (observed x)) (pack (observed y)) +
      inner ℂ (pack (halo x)) (pack (halo y)) +
      inner ℂ (pack (escape x)) (pack (escape y)) :=
  (nativeNaimarkThreeSector_inner (pack x) (pack y)).symm.trans
    (quadratureThreeSector_pack_inner x y)

theorem pack_escape (x : Space NaimarkSpace) :
    pack (escape x) = nativeComplexGlobalNaimarkEscape (pack x) := by
  rw [escape, pack_lift, nativeComplexGlobalNaimarkEscape_eq_realComplexification]

def response (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) : Space NaimarkSpace :=
  unpack (canonicalCompletedC3AmbientResponseState z hs)

theorem response_escape_zero (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    escape (response z hs) = 0 := by
  have h : pack (escape (response z hs)) = pack (0 : Space NaimarkSpace) := by
    rw [pack_escape, response, pack_unpack, nativeCompletedAmbientResponse_globalEscape_zero]
    rfl
  exact congrArg unpack h

theorem response_eq_gamma_add_correction (z : ℂ) (hz : z.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re) :
    response z hs = unpack (canonicalCompletedC3PolarizedGammaState z hz) +
      unpack (canonicalCompletedC3AmbientTfvdResolvedCorrectionState z hz hs) := by
  exact congrArg unpack (canonicalCompletedC3AmbientResponseState_eq_gamma_add_correction z hz hs)

theorem resolvedCorrection_escape (z : ℂ) (hz : z.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re) :
    escape (unpack (canonicalCompletedC3AmbientTfvdResolvedCorrectionState z hz hs)) =
      -escape (unpack (canonicalCompletedC3PolarizedGammaState z hz)) := by
  have h := congrArg escape (response_eq_gamma_add_correction z hz hs)
  rw [response_escape_zero, map_add] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- Both ordered crosses cancel in BOTH real polarized forms. -/
theorem resolvedCorrection_escape_four_crosses (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re)
    (ht : 0 < (operatorHeightParameter w).re) :
    let g := fun q hq => escape (unpack (canonicalCompletedC3PolarizedGammaState q hq))
    let d := fun q hq hhalf => escape
      (unpack (canonicalCompletedC3AmbientTfvdResolvedCorrectionState q hq hhalf))
    (inner ℝ (g z hz) (g w hw) + inner ℝ (g z hz) (d w hw ht) +
      inner ℝ (d z hz hs) (g w hw) + inner ℝ (d z hz hs) (d w hw ht) = 0) ∧
    (inner ℝ (J (g z hz)) (g w hw) + inner ℝ (J (g z hz)) (d w hw ht) +
      inner ℝ (J (d z hz hs)) (g w hw) + inner ℝ (J (d z hz hs)) (d w hw ht) = 0) := by
  dsimp only
  simp only [resolvedCorrection_escape, map_neg, inner_neg_left, inner_neg_right]
  constructor <;> ring

/-- Metric and rotation form expose the two components of the SAME native
four-channel defect, with its original separation and argument order. -/
theorem nativeDefect_real_components (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip)
    (ht : operatorHeightParameter w ∈ genuineCriticalStrip) :
    let D := canonicalCompletedC3CoisometricWronskianFourChannelDefect z w hz hw hs.1 ht.1
    let W := completedGreenWronskian completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion w z
    let g := inner ℝ (response z hs.1) (response w ht.1)
    let omega := inner ℝ (J (response z hs.1)) (response w ht.1)
    D.re = (w - conj z).re * g - (w - conj z).im * omega - W.re ∧
      D.im = (w - conj z).re * omega + (w - conj z).im * g - W.im := by
  dsimp only
  have hD := canonicalCompletedC3CoisometricWronskianFourChannelDefect_eq_sub z w hz hw hs ht
  rw [canonicalCompletedC3CoisometricCompressedBoundaryReadout_eq_kernel,
    inner_completedC3SymplecticCameraState_eq_ambientResponseKernel] at hD
  have hK : canonicalCompletedC3AmbientResponseKernel z w hs.1 ht.1 =
      (inner ℝ (response z hs.1) (response w ht.1) : ℂ) +
        Complex.I * (inner ℝ (J (response z hs.1)) (response w ht.1) : ℂ) := by
    simpa only [response, pack_unpack, canonicalCompletedC3AmbientResponseKernel]
      using pack_inner (response z hs.1) (response w ht.1)
  rw [hK] at hD
  constructor
  · simpa [Complex.mul_re, Complex.mul_im] using congrArg Complex.re hD
  · simpa [Complex.mul_re, Complex.mul_im] using congrArg Complex.im hD

end
end CarrySelfAdjointOperator.RealFirstNative
