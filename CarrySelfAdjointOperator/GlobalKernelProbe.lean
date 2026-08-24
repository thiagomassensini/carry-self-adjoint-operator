import CarrySelfAdjointOperator.CompletedC3GreenWronskianSameState
import CarrySelfAdjointOperator.CompletedGreenJetCoefficientRecurrence
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Global completed-kernel extension probe

This file separates two questions that must not be conflated:

1. whether the raw C3 camera coefficient can be renamed as the centered
   height coefficient while retaining the same completed Gram state;
2. whether a polarized Green--Wronskian identity proved away from zeros
   extends continuously to the full completed-height domain.

The quarter-point witness rules out the first shortcut.  The remaining
results give the exact off-zero sewing interface and prove its extension to
zeros from analyticity, continuity, and density of the nonzero locus.  No
off-zero sewing instance for the canonical C3 state is postulated here.
-/

open scoped ComplexConjugate Topology

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera

noncomputable section

private theorem quarter_mem_genuineCriticalStrip :
    (1 / 4 : ℂ) ∈ genuineCriticalStrip := by
  constructor <;> norm_num

private theorem quarter_re_pos :
    0 < (1 / 4 : ℂ).re := by
  norm_num

theorem c3RawCameraCoefficient_quarter_eq_zero :
    NativeCarryC3Crosswalk.c3RawCameraEigenvalue (1 / 4 : ℂ) -
        (starRingEnd ℂ)
          (NativeCarryC3Crosswalk.c3RawCameraEigenvalue (1 / 4 : ℂ)) = 0 := by
  rw [show (starRingEnd ℂ)
        (NativeCarryC3Crosswalk.c3RawCameraEigenvalue (1 / 4 : ℂ)) =
      NativeCarryC3Crosswalk.c3RawCameraEigenvalue (1 / 4 : ℂ) by
    simp [NativeCarryC3Crosswalk.c3RawCameraEigenvalue,
      natDirichletTerm, dirichletTerm]
    have hpow :
        (3 : ℂ) ^ (-4⁻¹ : ℂ) =
          (((3 : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (show (0 : ℝ) ≤ 3 by norm_num)]
      norm_num
    rw [hpow]
    simp]
  exact sub_self _

theorem centeredHeightCoefficient_quarter_ne_zero :
    centeredHeightParameter (1 / 4 : ℂ) -
        (starRingEnd ℂ) (centeredHeightParameter (1 / 4 : ℂ)) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  norm_num [centeredHeightParameter, Complex.mul_im] at him

theorem positiveDirichletGradient_quarter_zero_ne_zero :
    positiveDirichletGradient (1 / 4 : ℂ) 0 ≠ 0 := by
  intro hgradient
  have hedge := finiteReflectedGradientEdge_re_pos
    quarter_mem_genuineCriticalStrip 0
  rw [finiteReflectedGradientEdge] at hedge
  rw [hgradient] at hedge
  norm_num at hedge

theorem canonicalCompletedC3DirichletGradientState_quarter_ne_zero :
    canonicalCompletedC3DirichletGradientState
        (1 / 4 : ℂ) quarter_re_pos ≠ 0 := by
  intro hstate
  have hcoordinate := congrArg
    (fun state : CarryVerticalL2 => state 0) hstate
  simp only [canonicalCompletedC3DirichletGradientState_apply] at hcoordinate
  exact positiveDirichletGradient_quarter_zero_ne_zero hcoordinate

theorem canonicalCompletedC3RawGammaGram_quarter_ne_zero :
    canonicalCompletedC3RawGammaGram
        (1 / 4 : ℂ) (1 / 4 : ℂ) quarter_re_pos quarter_re_pos ≠ 0 := by
  unfold canonicalCompletedC3RawGammaGram
  exact inner_self_ne_zero.mpr
    canonicalCompletedC3DirichletGradientState_quarter_ne_zero

/-- The raw positive Gram is nonzero where its raw Green coefficient is zero
but the centered-height Green coefficient is nonzero.  Therefore the raw
two-variable identity cannot become the completed height-kernel identity by
mere coefficient renaming. -/
theorem centeredHeightCoefficient_mul_rawGammaGram_quarter_ne_zero :
    (centeredHeightParameter (1 / 4 : ℂ) -
        (starRingEnd ℂ) (centeredHeightParameter (1 / 4 : ℂ))) *
      canonicalCompletedC3RawGammaGram
        (1 / 4 : ℂ) (1 / 4 : ℂ) quarter_re_pos quarter_re_pos ≠ 0 :=
  mul_ne_zero centeredHeightCoefficient_quarter_ne_zero
    canonicalCompletedC3RawGammaGram_quarter_ne_zero

/-- The comparison point belongs to the nonzero locus of the completed
characteristic. -/
theorem completedNativeOperatorCharacteristic_centeredQuarter_ne_zero :
    completedNativeOperatorCharacteristic
        (centeredHeightParameter (1 / 4 : ℂ)) ≠ 0 := by
  unfold completedNativeOperatorCharacteristic
  apply mul_ne_zero
  · apply nativeXiCompletionFactor_ne_zero
    simpa using quarter_mem_genuineCriticalStrip
  · rw [operatorHeightParameter_centeredHeightParameter]
    rw [nativeScalar_eq_genuineContinuation quarter_mem_genuineCriticalStrip]
    have hcast : (((1 : ℝ) / 4 : ℝ) : ℂ) = (1 / 4 : ℂ) := by
      norm_num
    rw [← hcast]
    exact genuineContinuation_ofReal_ne_zero
      (σ := (1 : ℝ) / 4) (by norm_num) (by norm_num)

/-- Even away from completed-characteristic zeros, the raw camera coefficient
cannot be replaced by the centered spectral coefficient while retaining the
same positive Gram kernel. -/
theorem rawCameraGreenCoefficient_mul_gram_ne_centeredHeightCoefficient_mul_gram :
    (NativeCarryC3Crosswalk.c3RawCameraEigenvalue (1 / 4 : ℂ) -
          (starRingEnd ℂ)
            (NativeCarryC3Crosswalk.c3RawCameraEigenvalue (1 / 4 : ℂ))) *
        canonicalCompletedC3RawGammaGram
          (1 / 4 : ℂ) (1 / 4 : ℂ) quarter_re_pos quarter_re_pos ≠
      (centeredHeightParameter (1 / 4 : ℂ) -
          (starRingEnd ℂ) (centeredHeightParameter (1 / 4 : ℂ))) *
        canonicalCompletedC3RawGammaGram
          (1 / 4 : ℂ) (1 / 4 : ℂ) quarter_re_pos quarter_re_pos := by
  rw [c3RawCameraCoefficient_quarter_eq_zero, zero_mul]
  exact centeredHeightCoefficient_mul_rawGammaGram_quarter_ne_zero.symm

/-! ## Off-zero polarized kernel interface -/

/-- The positive Green kernel associated with a complex Hilbert state. -/
def completedPositiveGreenKernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (state : ℂ → E) (z w : ℂ) : ℂ :=
  (z - (starRingEnd ℂ) w) * inner ℂ (state w) (state z)

/-- Division-free Green representation required only where both scalar traces
are nonzero. -/
def HasOffZeroDivisionFreeGreenRepresentationOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (domain : Set ℂ) (F Psi : ℂ → ℂ) (state : ℂ → E) : Prop :=
  ∀ z ∈ domain, F z ≠ 0 → ∀ w ∈ domain, F w ≠ 0 →
    completedGreenWronskian F Psi z w =
      completedPositiveGreenKernel state z w

/-- Four polarized ledger channels. They remain distinct until the final
scalar readout. -/
structure PolarizedCompletedC3KernelChannels where
  radialGreen : ℂ → ℂ → ℂ
  wronskianSkew : ℂ → ℂ → ℂ
  offDiagonal : ℂ → ℂ → ℂ
  seamDefect : ℂ → ℂ → ℂ

/-- Channel-local final scalar readout of a polarized ledger. -/
def PolarizedCompletedC3KernelChannels.finalScalarReadout
    (channels : PolarizedCompletedC3KernelChannels) (z w : ℂ) : ℂ :=
  channels.radialGreen z w +
    channels.wronskianSkew z w +
    channels.offDiagonal z w +
    channels.seamDefect z w

/-- The exact off-zero sewing contract: the separated ledger first reads as
the trace Wronskian and, independently, as the positive Gram Green kernel. -/
def HasOffZeroSeparatedCompletedC3KernelSewing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (domain : Set ℂ) (F Psi : ℂ → ℂ) (state : ℂ → E)
    (channels : PolarizedCompletedC3KernelChannels) : Prop :=
  ∀ z ∈ domain, F z ≠ 0 → ∀ w ∈ domain, F w ≠ 0 →
    completedGreenWronskian F Psi z w =
        channels.finalScalarReadout z w ∧
      channels.finalScalarReadout z w =
        completedPositiveGreenKernel state z w

theorem HasOffZeroSeparatedCompletedC3KernelSewing.toGreenRepresentation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {domain : Set ℂ} {F Psi : ℂ → ℂ} {state : ℂ → E}
    {channels : PolarizedCompletedC3KernelChannels}
    (hsewing : HasOffZeroSeparatedCompletedC3KernelSewing
      domain F Psi state channels) :
    HasOffZeroDivisionFreeGreenRepresentationOn domain F Psi state := by
  intro z hzDomain hz w hwDomain hw
  exact (hsewing z hzDomain hz w hwDomain hw).1.trans
    (hsewing z hzDomain hz w hwDomain hw).2

/-- Cross-multiplied relation between the trace Wronskian and the normalized
response. It is valid at every pair of nonzero scalar values. -/
theorem completedGreenWronskian_eq_normalizedResponse_cross_mul
    (F Psi : ℂ → ℂ) (z w : ℂ) (hz : F z ≠ 0) (hw : F w ≠ 0) :
    completedGreenWronskian F Psi z w =
      ((2 : ℂ) * (starRingEnd ℂ) (F w) * F z) *
        (completedGreenNormalizedResponse F Psi z -
          (starRingEnd ℂ) (completedGreenNormalizedResponse F Psi w)) := by
  have hstar : (starRingEnd ℂ) (F w) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hw
  unfold completedGreenNormalizedResponse completedGreenWronskian
  simp only [map_div₀, map_mul, map_ofNat]
  field_simp [hz, hw, hstar]

/-- On the nonzero locus, the division-free Green identity is equivalent to
the polarized normalized-response identity. No statement at a zero is used. -/
theorem offZeroGreenRepresentation_iff_normalizedPolarizedResponse
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (domain : Set ℂ) (F Psi : ℂ → ℂ) (state : ℂ → E) :
    HasOffZeroDivisionFreeGreenRepresentationOn domain F Psi state ↔
      ∀ z ∈ domain, F z ≠ 0 → ∀ w ∈ domain, F w ≠ 0 →
        (z - (starRingEnd ℂ) w) *
            inner ℂ
              (normalizedCompletedGreenState F state w)
              (normalizedCompletedGreenState F state z) =
          completedGreenNormalizedResponse F Psi z -
            (starRingEnd ℂ) (completedGreenNormalizedResponse F Psi w) := by
  constructor
  · intro hgreen z hzDomain hz w hwDomain hw
    have hstar : (starRingEnd ℂ) (F w) ≠ 0 :=
      (map_ne_zero (starRingEnd ℂ)).2 hw
    have hscale :
        (2 : ℂ) * (starRingEnd ℂ) (F w) * F z ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hstar) hz
    apply mul_left_cancel₀ hscale
    calc
      ((2 : ℂ) * (starRingEnd ℂ) (F w) * F z) *
          ((z - (starRingEnd ℂ) w) *
            inner ℂ
              (normalizedCompletedGreenState F state w)
              (normalizedCompletedGreenState F state z)) =
        (z - (starRingEnd ℂ) w) *
          (((2 : ℂ) * (starRingEnd ℂ) (F w) * F z) *
            inner ℂ
              (normalizedCompletedGreenState F state w)
              (normalizedCompletedGreenState F state z)) := by ring
      _ = (z - (starRingEnd ℂ) w) * inner ℂ (state w) (state z) := by
        rw [normalizedCompletedGreenState_inner_cross_mul
          F state z w hz hw]
      _ = completedGreenWronskian F Psi z w :=
        (hgreen z hzDomain hz w hwDomain hw).symm
      _ = ((2 : ℂ) * (starRingEnd ℂ) (F w) * F z) *
          (completedGreenNormalizedResponse F Psi z -
            (starRingEnd ℂ)
              (completedGreenNormalizedResponse F Psi w)) :=
        completedGreenWronskian_eq_normalizedResponse_cross_mul
          F Psi z w hz hw
  · intro hresponse z hzDomain hz w hwDomain hw
    calc
      completedGreenWronskian F Psi z w =
          ((2 : ℂ) * (starRingEnd ℂ) (F w) * F z) *
            (completedGreenNormalizedResponse F Psi z -
              (starRingEnd ℂ)
                (completedGreenNormalizedResponse F Psi w)) :=
        completedGreenWronskian_eq_normalizedResponse_cross_mul
          F Psi z w hz hw
      _ = ((2 : ℂ) * (starRingEnd ℂ) (F w) * F z) *
          ((z - (starRingEnd ℂ) w) *
            inner ℂ
              (normalizedCompletedGreenState F state w)
              (normalizedCompletedGreenState F state z)) := by
        rw [hresponse z hzDomain hz w hwDomain hw]
      _ = (z - (starRingEnd ℂ) w) *
          (((2 : ℂ) * (starRingEnd ℂ) (F w) * F z) *
            inner ℂ
              (normalizedCompletedGreenState F state w)
              (normalizedCompletedGreenState F state z)) := by ring
      _ = (z - (starRingEnd ℂ) w) * inner ℂ (state w) (state z) := by
        rw [normalizedCompletedGreenState_inner_cross_mul
          F state z w hz hw]
      _ = completedPositiveGreenKernel state z w := rfl

/-- Nonzero points of a scalar trace inside a selected domain. -/
def completedTraceNonzeroLocus (domain : Set ℂ) (F : ℂ → ℂ) : Set ℂ :=
  {z | z ∈ domain ∧ F z ≠ 0}

theorem isPreconnected_genuineCriticalStrip :
    IsPreconnected genuineCriticalStrip := by
  change IsPreconnected ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.re < 1})
  exact ((convex_halfSpace_re_gt 0).inter
    (convex_halfSpace_re_lt 1)).isPreconnected

/-- The nonzero locus of the Genuine continuation is dense relative to the
open critical strip. -/
theorem genuineCriticalStrip_subset_closure_nonzeroLocus :
    genuineCriticalStrip ⊆
      closure (completedTraceNonzeroLocus
        genuineCriticalStrip genuineContinuation) := by
  intro s hs
  rw [mem_closure_iff_frequently]
  by_contra hfrequent
  have hnone :
      ∀ᶠ u in 𝓝 s,
        ¬(u ∈ genuineCriticalStrip ∧ genuineContinuation u ≠ 0) :=
    Filter.not_frequently.mp hfrequent
  have hstrip : ∀ᶠ u in 𝓝 s, u ∈ genuineCriticalStrip :=
    isOpen_genuineCriticalStrip.mem_nhds hs
  have hlocalZero : ∀ᶠ u in 𝓝 s, genuineContinuation u = 0 := by
    filter_upwards [hnone, hstrip] with u huNone huStrip
    by_contra huNonzero
    exact huNone ⟨huStrip, huNonzero⟩
  have hlocalZeroFunction :
      genuineContinuation =ᶠ[𝓝 s] (0 : ℂ → ℂ) := by
    filter_upwards [hlocalZero] with u hu
    simpa using hu
  have hglobalZero :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      analyticOnNhd_genuineContinuation_genuineCriticalStrip
      isPreconnected_genuineCriticalStrip hs hlocalZeroFunction
  have hhalf : (((1 : ℝ) / 2 : ℝ) : ℂ) ∈ genuineCriticalStrip := by
    constructor <;> norm_num
  apply genuineContinuation_ofReal_ne_zero
    (σ := (1 : ℝ) / 2) (by norm_num) (by norm_num)
  simpa using hglobalZero hhalf

/-- The nonzero locus of the completed characteristic is dense relative to
the centered-height strip. Completion factors introduce no zero there. -/
theorem completedNativeHeightDomain_subset_closure_nonzeroLocus :
    completedNativeHeightDomain ⊆
      closure (completedTraceNonzeroLocus
        completedNativeHeightDomain completedNativeOperatorCharacteristic) := by
  intro z hz
  have hsClosure :=
    genuineCriticalStrip_subset_closure_nonzeroLocus hz
  have hcenteredContinuous : Continuous centeredHeightParameter := by
    unfold centeredHeightParameter
    fun_prop
  have hmaps : Set.MapsTo centeredHeightParameter
      (completedTraceNonzeroLocus genuineCriticalStrip genuineContinuation)
      (completedTraceNonzeroLocus completedNativeHeightDomain
        completedNativeOperatorCharacteristic) := by
    intro s hs
    constructor
    · change operatorHeightParameter (centeredHeightParameter s) ∈
        genuineCriticalStrip
      simpa using hs.1
    · unfold completedNativeOperatorCharacteristic
      apply mul_ne_zero
      · apply nativeXiCompletionFactor_ne_zero
        simpa using hs.1
      · rw [operatorHeightParameter_centeredHeightParameter]
        rw [nativeScalar_eq_genuineContinuation hs.1]
        exact hs.2
  have hmapped := map_mem_closure
    hcenteredContinuous hsClosure hmaps
  have hinverse :
      centeredHeightParameter (operatorHeightParameter z) = z := by
    apply Complex.ext <;>
      simp [centeredHeightParameter, operatorHeightParameter]
  rw [hinverse] at hmapped
  exact hmapped

/-- The centered-height strip is open. -/
theorem isOpen_completedNativeHeightDomain :
    IsOpen completedNativeHeightDomain := by
  unfold completedNativeHeightDomain
  apply isOpen_genuineCriticalStrip.preimage
  unfold operatorHeightParameter
  fun_prop

/-- The concrete completed characteristic is analytic at every point of its
natural centered-height domain. -/
theorem completedNativeOperatorCharacteristic_analyticAt
    {z : ℂ} (hz : z ∈ completedNativeHeightDomain) :
    AnalyticAt ℂ completedNativeOperatorCharacteristic z := by
  have hdiff : DifferentiableOn ℂ completedNativeOperatorCharacteristic
      completedNativeHeightDomain := by
    intro u hu
    have hnativeDomain :
        operatorHeightParameter u ∈ nativeScalarDomain :=
      ⟨lt_trans (by norm_num) hu.1, hu.2⟩
    have hproduct :=
      (nativeXiCompletionFactor_differentiableAt hu).mul
        (nativeHeightScalar_differentiableAt hnativeDomain)
    exact hproduct.differentiableWithinAt
  exact hdiff.analyticAt (isOpen_completedNativeHeightDomain.mem_nhds hz)

/-- A Wronskian is continuous on a product domain whenever both of its trace
coordinates are continuous at every point of that domain. -/
theorem completedGreenWronskian_continuousOn
    {domain : Set ℂ} {F Psi : ℂ → ℂ}
    (hF : ∀ z ∈ domain, ContinuousAt F z)
    (hPsi : ∀ z ∈ domain, ContinuousAt Psi z) :
    ContinuousOn (Function.uncurry (completedGreenWronskian F Psi))
      (domain ×ˢ domain) := by
  rintro ⟨z, w⟩ ⟨hz, hw⟩
  have hFLeft : ContinuousAt (fun p : ℂ × ℂ => F p.1) (z, w) :=
    (hF z hz).comp continuousAt_fst
  have hFRight : ContinuousAt (fun p : ℂ × ℂ => F p.2) (z, w) :=
    (hF w hw).comp continuousAt_snd
  have hPsiLeft : ContinuousAt (fun p : ℂ × ℂ => Psi p.1) (z, w) :=
    (hPsi z hz).comp continuousAt_fst
  have hPsiRight : ContinuousAt (fun p : ℂ × ℂ => Psi p.2) (z, w) :=
    (hPsi w hw).comp continuousAt_snd
  have hcontinuous : ContinuousAt
      (Function.uncurry (completedGreenWronskian F Psi)) (z, w) := by
    change ContinuousAt
      (fun p : ℂ × ℂ =>
        Psi p.1 * (starRingEnd ℂ) (F p.2) -
          F p.1 * (starRingEnd ℂ) (Psi p.2)) (z, w)
    exact (hPsiLeft.mul hFRight.star).sub (hFLeft.mul hPsiRight.star)
  exact hcontinuous.continuousWithinAt

/-- The actual Wronskian of `(F,-F')` is continuous on the completed native
height strip. -/
theorem completedNativeFNegFPrimeWronskian_continuousOn :
    ContinuousOn
      (Function.uncurry
        (completedGreenWronskian
          completedNativeOperatorCharacteristic
          (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)))
      (completedNativeHeightDomain ×ˢ completedNativeHeightDomain) := by
  apply completedGreenWronskian_continuousOn
  · intro z hz
    exact (completedNativeOperatorCharacteristic_analyticAt hz).continuousAt
  · intro z hz
    exact
      (completedNativeOperatorCharacteristic_analyticAt hz).deriv.neg.continuousAt

/-- Equality of the separated readout and both global kernels extends from
the nonzero locus to its closure. This is the step that permits specialization
at a zero without inserting a zero-local equivalence. -/
theorem offZeroSeparatedCompletedC3KernelSewing_extends
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {domain : Set ℂ} {F Psi : ℂ → ℂ} {state : ℂ → E}
    {channels : PolarizedCompletedC3KernelChannels}
    (hsewing : HasOffZeroSeparatedCompletedC3KernelSewing
      domain F Psi state channels)
    (hclosure : domain ⊆ closure (completedTraceNonzeroLocus domain F))
    (hwronskian : Continuous (Function.uncurry
      (completedGreenWronskian F Psi)))
    (hreadout : Continuous (Function.uncurry
      channels.finalScalarReadout))
    (hgram : Continuous (Function.uncurry
      (completedPositiveGreenKernel state))) :
    ∀ z ∈ domain, ∀ w ∈ domain,
      completedGreenWronskian F Psi z w =
          channels.finalScalarReadout z w ∧
        channels.finalScalarReadout z w =
          completedPositiveGreenKernel state z w := by
  let nonzeroDomain := completedTraceNonzeroLocus domain F
  have hwronskianReadout :
      ∀ z ∈ closure nonzeroDomain, ∀ w ∈ closure nonzeroDomain,
        completedGreenWronskian F Psi z w =
          channels.finalScalarReadout z w := by
    apply eqOn_closure₂
    · intro z hz w hw
      exact (hsewing z hz.1 hz.2 w hw.1 hw.2).1
    · exact hwronskian
    · exact hreadout
  have hreadoutGram :
      ∀ z ∈ closure nonzeroDomain, ∀ w ∈ closure nonzeroDomain,
        channels.finalScalarReadout z w =
          completedPositiveGreenKernel state z w := by
    apply eqOn_closure₂
    · intro z hz w hw
      exact (hsewing z hz.1 hz.2 w hw.1 hw.2).2
    · exact hreadout
    · exact hgram
  intro z hzDomain w hwDomain
  exact ⟨hwronskianReadout z (hclosure hzDomain) w (hclosure hwDomain),
    hreadoutGram z (hclosure hzDomain) w (hclosure hwDomain)⟩

/-- Domain-local closure variant. Only continuity on `domain × domain` is
required. -/
theorem offZeroSeparatedCompletedC3KernelSewing_extendsOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {domain : Set ℂ} {F Psi : ℂ → ℂ} {state : ℂ → E}
    {channels : PolarizedCompletedC3KernelChannels}
    (hsewing : HasOffZeroSeparatedCompletedC3KernelSewing
      domain F Psi state channels)
    (hclosure : domain ⊆ closure (completedTraceNonzeroLocus domain F))
    (hwronskian : ContinuousOn (Function.uncurry
      (completedGreenWronskian F Psi)) (domain ×ˢ domain))
    (hreadout : ContinuousOn (Function.uncurry
      channels.finalScalarReadout) (domain ×ˢ domain))
    (hgram : ContinuousOn (Function.uncurry
      (completedPositiveGreenKernel state)) (domain ×ˢ domain)) :
    ∀ z ∈ domain, ∀ w ∈ domain,
      completedGreenWronskian F Psi z w =
          channels.finalScalarReadout z w ∧
        channels.finalScalarReadout z w =
          completedPositiveGreenKernel state z w := by
  let nonzeroDomain := completedTraceNonzeroLocus domain F
  have hnonzeroSubset :
      nonzeroDomain ×ˢ nonzeroDomain ⊆ domain ×ˢ domain := by
    rintro ⟨z, w⟩ ⟨hz, hw⟩
    exact ⟨hz.1, hw.1⟩
  have hdomainClosure :
      domain ×ˢ domain ⊆ closure (nonzeroDomain ×ˢ nonzeroDomain) := by
    rintro ⟨z, w⟩ ⟨hz, hw⟩
    rw [closure_prod_eq]
    exact ⟨hclosure hz, hclosure hw⟩
  have hwronskianReadout : Set.EqOn
      (Function.uncurry (completedGreenWronskian F Psi))
      (Function.uncurry channels.finalScalarReadout)
      (domain ×ˢ domain) := by
    apply Set.EqOn.of_subset_closure
      (s := nonzeroDomain ×ˢ nonzeroDomain)
    · rintro ⟨z, w⟩ ⟨hz, hw⟩
      exact (hsewing z hz.1 hz.2 w hw.1 hw.2).1
    · exact hwronskian
    · exact hreadout
    · exact hnonzeroSubset
    · exact hdomainClosure
  have hreadoutGram : Set.EqOn
      (Function.uncurry channels.finalScalarReadout)
      (Function.uncurry (completedPositiveGreenKernel state))
      (domain ×ˢ domain) := by
    apply Set.EqOn.of_subset_closure
      (s := nonzeroDomain ×ˢ nonzeroDomain)
    · rintro ⟨z, w⟩ ⟨hz, hw⟩
      exact (hsewing z hz.1 hz.2 w hw.1 hw.2).2
    · exact hreadout
    · exact hgram
    · exact hnonzeroSubset
    · exact hdomainClosure
  intro z hzDomain w hwDomain
  have hp : (z, w) ∈ domain ×ˢ domain := ⟨hzDomain, hwDomain⟩
  have hleft := hwronskianReadout hp
  have hright := hreadoutGram hp
  change completedGreenWronskian F Psi z w =
    channels.finalScalarReadout z w at hleft
  change channels.finalScalarReadout z w =
    completedPositiveGreenKernel state z w at hright
  exact ⟨hleft, hright⟩

/-- Local-continuity version of post-extension zero confinement. -/
theorem zero_im_eq_zero_of_offZeroSeparatedKernelSewingOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {domain : Set ℂ} {F Psi : ℂ → ℂ} {state : ℂ → E}
    {channels : PolarizedCompletedC3KernelChannels} {z : ℂ}
    (hsewing : HasOffZeroSeparatedCompletedC3KernelSewing
      domain F Psi state channels)
    (hclosure : domain ⊆ closure (completedTraceNonzeroLocus domain F))
    (hwronskian : ContinuousOn (Function.uncurry
      (completedGreenWronskian F Psi)) (domain ×ˢ domain))
    (hreadout : ContinuousOn (Function.uncurry
      channels.finalScalarReadout) (domain ×ˢ domain))
    (hgram : ContinuousOn (Function.uncurry
      (completedPositiveGreenKernel state)) (domain ×ˢ domain))
    (hzDomain : z ∈ domain) (hzero : F z = 0) (hstate : state z ≠ 0) :
    z.im = 0 := by
  have hglobal := offZeroSeparatedCompletedC3KernelSewing_extendsOn
    hsewing hclosure hwronskian hreadout hgram z hzDomain z hzDomain
  have hkernel :
      completedGreenWronskian F Psi z z =
        completedPositiveGreenKernel state z z :=
    hglobal.1.trans hglobal.2
  have hwronskianZero : completedGreenWronskian F Psi z z = 0 := by
    simp [completedGreenWronskian, hzero]
  have hproduct :
      (z - (starRingEnd ℂ) z) * inner ℂ (state z) (state z) = 0 := by
    change completedPositiveGreenKernel state z z = 0
    rw [← hkernel, hwronskianZero]
  have hinner : inner ℂ (state z) (state z) ≠ 0 :=
    inner_self_ne_zero.mpr hstate
  have hfixed : z = (starRingEnd ℂ) z :=
    sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right hinner)
  have him := congrArg Complex.im hfixed
  simp only [Complex.conj_im] at him
  linarith

/-- After off-zero sewing has been extended, a zero carrying a nonzero state
is fixed by conjugation. The proof invokes the zero only after the global
kernel equality has already been obtained. -/
theorem zero_fixedByConjugation_of_offZeroSeparatedKernelSewing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {domain : Set ℂ} {F Psi : ℂ → ℂ} {state : ℂ → E}
    {channels : PolarizedCompletedC3KernelChannels} {z : ℂ}
    (hsewing : HasOffZeroSeparatedCompletedC3KernelSewing
      domain F Psi state channels)
    (hclosure : domain ⊆ closure (completedTraceNonzeroLocus domain F))
    (hwronskian : Continuous (Function.uncurry
      (completedGreenWronskian F Psi)))
    (hreadout : Continuous (Function.uncurry
      channels.finalScalarReadout))
    (hgram : Continuous (Function.uncurry
      (completedPositiveGreenKernel state)))
    (hzDomain : z ∈ domain) (hzero : F z = 0) (hstate : state z ≠ 0) :
    z = (starRingEnd ℂ) z := by
  have hglobal := offZeroSeparatedCompletedC3KernelSewing_extends
    hsewing hclosure hwronskian hreadout hgram z hzDomain z hzDomain
  have hkernel :
      completedGreenWronskian F Psi z z =
        completedPositiveGreenKernel state z z :=
    hglobal.1.trans hglobal.2
  have hwronskianZero : completedGreenWronskian F Psi z z = 0 := by
    simp [completedGreenWronskian, hzero]
  have hproduct :
      (z - (starRingEnd ℂ) z) * inner ℂ (state z) (state z) = 0 := by
    change completedPositiveGreenKernel state z z = 0
    rw [← hkernel, hwronskianZero]
  have hinner : inner ℂ (state z) (state z) ≠ 0 :=
    inner_self_ne_zero.mpr hstate
  exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right hinner)

/-- Coordinate form of the same post-extension specialization. -/
theorem zero_im_eq_zero_of_offZeroSeparatedKernelSewing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {domain : Set ℂ} {F Psi : ℂ → ℂ} {state : ℂ → E}
    {channels : PolarizedCompletedC3KernelChannels} {z : ℂ}
    (hsewing : HasOffZeroSeparatedCompletedC3KernelSewing
      domain F Psi state channels)
    (hclosure : domain ⊆ closure (completedTraceNonzeroLocus domain F))
    (hwronskian : Continuous (Function.uncurry
      (completedGreenWronskian F Psi)))
    (hreadout : Continuous (Function.uncurry
      channels.finalScalarReadout))
    (hgram : Continuous (Function.uncurry
      (completedPositiveGreenKernel state)))
    (hzDomain : z ∈ domain) (hzero : F z = 0) (hstate : state z ≠ 0) :
    z.im = 0 := by
  have hfixed := zero_fixedByConjugation_of_offZeroSeparatedKernelSewing
    hsewing hclosure hwronskian hreadout hgram hzDomain hzero hstate
  have him := congrArg Complex.im hfixed
  simp only [Complex.conj_im] at him
  linarith

/-! ## Concrete completed `(F,-F')` gate -/

/-- Off-zero global-kernel sewing for the actual completed characteristic and
its canonical companion. -/
def HasCompletedNativeFNegFPrimeGlobalKernelSewingOffZeros
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (state : ℂ → E) (channels : PolarizedCompletedC3KernelChannels) : Prop :=
  HasOffZeroSeparatedCompletedC3KernelSewing
    completedNativeHeightDomain
    completedNativeOperatorCharacteristic
    (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
    state channels

/-- An independently proved off-zero sewing identity extends to the full
completed strip. All four channels remain present in the middle equality. -/
theorem completedNativeFNegFPrime_globalKernelIdentity_of_offZeroSewing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {state : ℂ → E} {channels : PolarizedCompletedC3KernelChannels}
    (hsewing : HasCompletedNativeFNegFPrimeGlobalKernelSewingOffZeros
      state channels)
    (hreadout : ContinuousOn (Function.uncurry
      channels.finalScalarReadout)
      (completedNativeHeightDomain ×ˢ completedNativeHeightDomain))
    (hgram : ContinuousOn (Function.uncurry
      (completedPositiveGreenKernel state))
      (completedNativeHeightDomain ×ˢ completedNativeHeightDomain)) :
    ∀ z ∈ completedNativeHeightDomain,
      ∀ w ∈ completedNativeHeightDomain,
        completedGreenWronskian
            completedNativeOperatorCharacteristic
            (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
            z w = channels.finalScalarReadout z w ∧
          channels.finalScalarReadout z w =
            completedPositiveGreenKernel state z w :=
  offZeroSeparatedCompletedC3KernelSewing_extendsOn
    hsewing
    completedNativeHeightDomain_subset_closure_nonzeroLocus
    completedNativeFNegFPrimeWronskian_continuousOn
    hreadout hgram

/-- Only after the off-zero identity has been globally extended do we
specialize at a completed-characteristic zero. -/
theorem completedNativeZero_im_eq_zero_of_offZeroGlobalKernelSewing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {state : ℂ → E} {channels : PolarizedCompletedC3KernelChannels}
    (hsewing : HasCompletedNativeFNegFPrimeGlobalKernelSewingOffZeros
      state channels)
    (hreadout : ContinuousOn (Function.uncurry
      channels.finalScalarReadout)
      (completedNativeHeightDomain ×ˢ completedNativeHeightDomain))
    (hgram : ContinuousOn (Function.uncurry
      (completedPositiveGreenKernel state))
      (completedNativeHeightDomain ×ˢ completedNativeHeightDomain))
    {z : ℂ} (hz : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0)
    (hstate : state z ≠ 0) :
    z.im = 0 :=
  zero_im_eq_zero_of_offZeroSeparatedKernelSewingOn
    hsewing
    completedNativeHeightDomain_subset_closure_nonzeroLocus
    completedNativeFNegFPrimeWronskian_continuousOn
    hreadout hgram hz hzero hstate

end

end CarrySelfAdjointOperator
