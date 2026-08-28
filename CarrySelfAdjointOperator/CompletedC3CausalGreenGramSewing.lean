import CarrySelfAdjointOperator.CompletedC3DirichletGradientBracketSource
import CarrySelfAdjointOperator.CompletedC3RawSpectralTraceTransport
import Mathlib.Tactic

/-!
# Completed causal Green Gram sewing

The weighted causal Green response is only the interior coordinate of the
complete TFVD reconstruction.  The boundary return must remain present when
the reconstructed state is read in the Hilbert product.  This file packages
the final addition as one bounded readout and records its positive adjoint
square before expanding the resulting four channel blocks.

The completed raw C3 Gram and the limit of the finite raw Green pairing are
then identified with this same channel-complete form.  No boundary coordinate
is discarded and no equality with a logarithmic resolvent is assumed.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

noncomputable section

/-- Final bounded readout from the separated causal-response and boundary
channels to the reconstructed vertical TFVD state. -/
def canonicalCompletedC3CausalGreenBoundarySum :
    CanonicalCompletedC3CausalGreenBoundaryCarrier →L[ℂ] CarryVerticalL2 :=
  (ContinuousLinearMap.fst ℂ CarryVerticalL2 CarryVerticalL2 +
      ContinuousLinearMap.snd ℂ CarryVerticalL2 CarryVerticalL2).comp
    (WithLp.prodContinuousLinearEquiv 2 ℂ
      CarryVerticalL2 CarryVerticalL2).toContinuousLinearMap

@[simp] theorem canonicalCompletedC3CausalGreenBoundarySum_apply
    (state : CanonicalCompletedC3CausalGreenBoundaryCarrier) :
    canonicalCompletedC3CausalGreenBoundarySum state =
      state.fst + state.snd :=
  by
    simp [canonicalCompletedC3CausalGreenBoundarySum]

/-- The Hilbert product after the final readout is exactly the positive form
of its adjoint square on the uncollapsed two-channel carrier. -/
theorem canonicalCompletedC3CausalGreenBoundarySum_inner_eq_adjointSquare
    (x y : CanonicalCompletedC3CausalGreenBoundaryCarrier) :
    inner ℂ
        (canonicalCompletedC3CausalGreenBoundarySum x)
        (canonicalCompletedC3CausalGreenBoundarySum y) =
      inner ℂ x
        (ContinuousLinearMap.adjoint
          canonicalCompletedC3CausalGreenBoundarySum
          (canonicalCompletedC3CausalGreenBoundarySum y)) := by
  exact (ContinuousLinearMap.adjoint_inner_right
    canonicalCompletedC3CausalGreenBoundarySum x
    (canonicalCompletedC3CausalGreenBoundarySum y)).symm

/-- The channel-complete adjoint-square form is nonnegative on the diagonal. -/
theorem canonicalCompletedC3CausalGreenBoundarySum_adjointSquare_re_nonneg
    (x : CanonicalCompletedC3CausalGreenBoundaryCarrier) :
    0 ≤ (inner ℂ x
      (ContinuousLinearMap.adjoint
        canonicalCompletedC3CausalGreenBoundarySum
        (canonicalCompletedC3CausalGreenBoundarySum x))).re := by
  rw [← canonicalCompletedC3CausalGreenBoundarySum_inner_eq_adjointSquare]
  rw [inner_self_eq_norm_sq_to_K]
  norm_num [pow_two]
  positivity

/-- The completed raw C3 Gram is the adjoint-square form of the final causal
response-plus-boundary readout.  This is the positive operator identity that
retains both channels and all cross terms. -/
theorem canonicalCompletedC3RawGammaGram_eq_causalAdjointSquare
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (s t : ℂ) (hs : 0 < s.re) (ht : 0 < t.re) :
    canonicalCompletedC3RawGammaGram s t hs ht =
      inner ℂ
        (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
          hbase s hs)
        (ContinuousLinearMap.adjoint
          canonicalCompletedC3CausalGreenBoundarySum
          (canonicalCompletedC3CausalGreenBoundarySum
            (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
              hbase t ht))) := by
  unfold canonicalCompletedC3RawGammaGram
  rw [← canonicalCompletedC3DirichletGradientCausalGreenBoundaryState_sum
      hbase s hs,
    ← canonicalCompletedC3DirichletGradientCausalGreenBoundaryState_sum
      hbase t ht]
  simpa only [canonicalCompletedC3CausalGreenBoundarySum_apply] using
    (canonicalCompletedC3CausalGreenBoundarySum_inner_eq_adjointSquare
      (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState hbase s hs)
      (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState hbase t ht))

/-- Explicit four-block expansion of the same completed C3 Gram.  In
particular, the raw response Gram `G_q†G_q` is only the first block. -/
theorem canonicalCompletedC3RawGammaGram_eq_causalFourChannel
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (s t : ℂ) (hs : 0 < s.re) (ht : 0 < t.re) :
    canonicalCompletedC3RawGammaGram s t hs ht =
      inner ℂ
          (canonicalCompletedC3DirichletGradientCausalGreenState base s hs)
          (canonicalCompletedC3DirichletGradientCausalGreenState base t ht) +
        inner ℂ
          (canonicalCompletedC3DirichletGradientCausalGreenState base s hs)
          (canonicalCompletedC3DirichletGradientBoundaryReturnState hbase t ht) +
        inner ℂ
          (canonicalCompletedC3DirichletGradientBoundaryReturnState hbase s hs)
          (canonicalCompletedC3DirichletGradientCausalGreenState base t ht) +
        inner ℂ
          (canonicalCompletedC3DirichletGradientBoundaryReturnState hbase s hs)
          (canonicalCompletedC3DirichletGradientBoundaryReturnState hbase t ht) := by
  unfold canonicalCompletedC3RawGammaGram
  rw [← canonicalCompletedC3DirichletGradient_causalGreen_add_boundary
      hbase s hs,
    ← canonicalCompletedC3DirichletGradient_causalGreen_add_boundary
      hbase t ht]
  simp only [inner_add_left, inner_add_right]
  ring

/-- Operator-expanded version of the four-channel sewing.  The first block
is written as the source pairing through `G_q†G_q`; the three boundary blocks
remain explicit. -/
theorem canonicalCompletedC3RawGammaGram_eq_sourceAdjointSquare_add_boundary
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (s t : ℂ) (hs : 0 < s.re) (ht : 0 < t.re) :
    canonicalCompletedC3RawGammaGram s t hs ht =
      inner ℂ
          (canonicalCompletedC3DirichletGradientBracketSourceState base s hs)
          (ContinuousLinearMap.adjoint
            (carryVerticalL2WeightedGreen
              (canonicalBR2CarryAmplitudeRatio base))
            (canonicalCompletedC3DirichletGradientCausalGreenState base t ht)) +
        inner ℂ
          (canonicalCompletedC3DirichletGradientCausalGreenState base s hs)
          (canonicalCompletedC3DirichletGradientBoundaryReturnState hbase t ht) +
        inner ℂ
          (canonicalCompletedC3DirichletGradientBoundaryReturnState hbase s hs)
          (canonicalCompletedC3DirichletGradientCausalGreenState base t ht) +
        inner ℂ
          (canonicalCompletedC3DirichletGradientBoundaryReturnState hbase s hs)
          (canonicalCompletedC3DirichletGradientBoundaryReturnState hbase t ht) := by
  rw [canonicalCompletedC3RawGammaGram_eq_causalFourChannel hbase s t hs ht,
    canonicalCompletedC3DirichletGradientCausalGreenState_inner_eq_source_adjointSquare]

/-- The finite raw C3 Green pairing converges to the same channel-complete
adjoint-square form, multiplied by its exact raw camera eigenvalue
separation. -/
theorem c3RawGreenPairing_tendsto_completed_causalAdjointSquare
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    {r s : ℂ} (hr : 0 < r.re) (hs : 0 < s.re) :
    Tendsto
      (fun M : ℕ ↦ NativeCarryC3Crosswalk.c3RawGreenPairing M r s)
      atTop
      (nhds
        ((NativeCarryC3Crosswalk.c3RawCameraEigenvalue s -
            (starRingEnd ℂ)
              (NativeCarryC3Crosswalk.c3RawCameraEigenvalue r)) *
          inner ℂ
            (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
              hbase r hr)
            (ContinuousLinearMap.adjoint
              canonicalCompletedC3CausalGreenBoundarySum
              (canonicalCompletedC3CausalGreenBoundarySum
                (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
                  hbase s hs))))) := by
  rw [← canonicalCompletedC3RawGammaGram_eq_causalAdjointSquare
    hbase r s hr hs]
  exact c3RawGreenPairing_tendsto_completed hr hs

/-! ## Valid transport to the centered spectral coefficient -/

/-- Positive radial energy read from the complete causal response/boundary
carrier after reflection. -/
def canonicalCompletedC3CausalAdjointSquareRadialEnergy
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (s : ℂ) (hs : s ∈ genuineCriticalStrip) : ℝ :=
  2 * cpRadialCofactor 3 (criticalDisplacement s.re) *
    (inner ℂ
      (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
        hbase s hs.1)
      (ContinuousLinearMap.adjoint
        canonicalCompletedC3CausalGreenBoundarySum
        (canonicalCompletedC3CausalGreenBoundarySum
          (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
            hbase (reflectedParameter s)
            (by
              simpa [reflectedParameter] using
                sub_pos.mpr hs.2))))).re

/-- After reflection and radial normalization, the previously constructed
raw-state energy is the real part of the same channel-complete adjoint-square
form, with its exact positive radial cofactor. -/
theorem canonicalCompletedC3RawStateRadialEnergy_eq_causalAdjointSquare
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    canonicalCompletedC3RawStateRadialEnergy s hs =
      canonicalCompletedC3CausalAdjointSquareRadialEnergy hbase s hs := by
  unfold canonicalCompletedC3RawStateRadialEnergy
    canonicalCompletedC3CausalAdjointSquareRadialEnergy
  rw [canonicalCompletedC3RawGammaGram_eq_causalAdjointSquare]

/-- The complete causal energy is the already constructed infinite radial
Green energy. -/
theorem canonicalCompletedC3CausalAdjointSquareRadialEnergy_eq_infinite
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    canonicalCompletedC3CausalAdjointSquareRadialEnergy hbase s hs =
      canonicalCompletedC3InfiniteRadialGreenEnergy s := by
  rw [← canonicalCompletedC3RawStateRadialEnergy_eq_causalAdjointSquare
      hbase hs,
    canonicalCompletedC3RawStateRadialEnergy_eq_infiniteEnergy hs]

/-- Although the response/boundary decomposition depends on the selected
supported base, its final adjoint-square energy does not. -/
theorem canonicalCompletedC3CausalAdjointSquareRadialEnergy_base_independent
    {base₁ base₂ : ℕ}
    (hbase₁ : FiniteNativeCarryOperator.Camera.IsSupported base₁)
    (hbase₂ : FiniteNativeCarryOperator.Camera.IsSupported base₂)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    canonicalCompletedC3CausalAdjointSquareRadialEnergy hbase₁ s hs =
      canonicalCompletedC3CausalAdjointSquareRadialEnergy hbase₂ s hs := by
  rw [canonicalCompletedC3CausalAdjointSquareRadialEnergy_eq_infinite
      hbase₁ hs,
    canonicalCompletedC3CausalAdjointSquareRadialEnergy_eq_infinite
      hbase₂ hs]

/-- Strict positivity of the same camera-independent causal energy. -/
theorem canonicalCompletedC3CausalAdjointSquareRadialEnergy_pos
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    0 < canonicalCompletedC3CausalAdjointSquareRadialEnergy hbase s hs := by
  rw [canonicalCompletedC3CausalAdjointSquareRadialEnergy_eq_infinite hbase hs]
  exact canonicalCompletedC3InfiniteRadialGreenEnergy_pos hs

/-- The centered spectral factor acts on the completed causal adjoint-square
only after the exact reflection, phase normalization, and radial cofactor
transport.  This is the valid replacement for the false raw-coefficient
renaming shortcut. -/
theorem canonicalCompletedC3NormalizedGreenLimitTrace_eq_causalSpectralForm
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    canonicalCompletedC3NormalizedGreenLimitTrace s =
      (centeredHeightParameter s -
          (starRingEnd ℂ) (centeredHeightParameter s)) *
        (canonicalCompletedC3CausalAdjointSquareRadialEnergy
          hbase s hs : ℂ) := by
  rw [canonicalCompletedC3NormalizedGreenLimitTrace_eq_rawStateSpectralForm hs,
    canonicalCompletedC3RawStateRadialEnergy_eq_causalAdjointSquare hbase hs]

/-! ## Exact comparison with the global Gamma/Cauchy readout -/

/-- Pointwise equality between the normalized causal Green limit and the
global Gamma/Cauchy boundary is equivalent to one concrete equality of
positive energies.  All spectral factors and rotations have already been
discharged. -/
theorem canonicalCompletedC3NormalizedGreenLimitTrace_eq_globalBoundary_iff_causalEnergy
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    let z := centeredHeightParameter s
    let hz : z.im ≠ 0 :=
      centeredHeightParameter_im_ne_zero_of_re_ne_half hoff
    canonicalCompletedC3NormalizedGreenLimitTrace s =
        canonicalCompletedC3GlobalBoundaryGreenTrace z hz ↔
      canonicalCompletedC3CausalAdjointSquareRadialEnergy hbase s hs =
        canonicalCompletedC3GammaEnergy z := by
  dsimp only
  rw [canonicalCompletedC3NormalizedGreenLimitTrace_eq_causalSpectralForm
      hbase hs,
    canonicalCompletedC3GlobalBoundaryGreenTrace_eq_energy]
  have hfactor :
      centeredHeightParameter s -
          (starRingEnd ℂ) (centeredHeightParameter s) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro hconj
    apply centeredHeightParameter_im_ne_zero_of_re_ne_half hoff
    exact Complex.conj_eq_iff_im.mp hconj.symm
  constructor
  · intro h
    have henergyComplex :
        (canonicalCompletedC3CausalAdjointSquareRadialEnergy
            hbase s hs : ℂ) =
          (canonicalCompletedC3GammaEnergy
            (centeredHeightParameter s) : ℂ) :=
      mul_left_cancel₀ hfactor h
    exact_mod_cast henergyComplex
  · intro h
    rw [h]

/-- Global spelling of the same concrete energy gate.  This theorem adds no
hypothesis: it identifies the existing global readout proposition with the
pointwise causal-adjoint-square/Gamma-energy equality. -/
theorem canonicalCompletedC3GlobalGreenReadoutIntertwining_iff_causalEnergy
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) :
    CanonicalCompletedC3GlobalGreenReadoutIntertwining ↔
      ∀ {s : ℂ}, ∀ hs : s ∈ genuineCriticalStrip,
        ∀ _hoff : s.re ≠ (1 : ℝ) / 2,
          canonicalCompletedC3CausalAdjointSquareRadialEnergy hbase s hs =
            canonicalCompletedC3GammaEnergy (centeredHeightParameter s) := by
  constructor
  · intro hreadout s hs hoff
    exact
      (canonicalCompletedC3NormalizedGreenLimitTrace_eq_globalBoundary_iff_causalEnergy
        hbase hs hoff).mp (hreadout hs hoff)
  · intro henergy s hs hoff
    exact
      (canonicalCompletedC3NormalizedGreenLimitTrace_eq_globalBoundary_iff_causalEnergy
        hbase hs hoff).mpr (henergy hs hoff)

end

end CarrySelfAdjointOperator
