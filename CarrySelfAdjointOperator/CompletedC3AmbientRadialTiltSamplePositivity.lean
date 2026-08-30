import CarrySelfAdjointOperator.CompletedC3CompressedGammaGramCorrection
import CarrySelfAdjointOperator.CompletedNativeRadialTiltSamplePositivity
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# Radial samples of the full ambient C3 response

The static six-camera Gamma source is not the strong limit of the causal
cutoff sources.  The completed ambient response is the source-matched carrier:
its source is `canonicalCompletedC3AmbientInducedSourceLimit`, including the
complementary Naimark channel, and its Green identity is already exact.

This file samples that carrier on a uniformly spaced positive-imaginary grid.
The step also depends on the finite matrix size so every sample stays in the
half-plane required by the completed TFVD construction.  Positivity and the
division-free ambient Green identity are unconditional.  The comparison with
the completed-native `dslope` is isolated as one source-matched boundary gate.
-/

namespace CarrySelfAdjointOperator

open scoped ComplexConjugate ComplexOrder InnerProductSpace
open Filter Topology

noncomputable section

/-- Real scale of the finite-level radial grid. -/
def canonicalCompletedC3AmbientRadialTiltScale (k N : ℕ) : ℝ :=
  ((2 * (N + 1) * (k + 1) : ℕ) : ℝ)⁻¹

/-- A finite-level radial step small enough that all `N` sample points remain
inside `0 < Re (operatorHeightParameter z)`. -/
def canonicalCompletedC3AmbientRadialTiltStep (k N : ℕ) : ℂ :=
  Complex.I * (canonicalCompletedC3AmbientRadialTiltScale k N : ℂ)

/-- The uniformly spaced positive-imaginary sample grid for the full ambient
response. -/
def canonicalCompletedC3AmbientRadialTiltPoint
    (k N : ℕ) (n : Fin N) : ℂ :=
  (((n : ℕ) + 1 : ℕ) : ℂ) *
    canonicalCompletedC3AmbientRadialTiltStep k N

@[simp] theorem canonicalCompletedC3AmbientRadialTiltPoint_re
    (k N : ℕ) (n : Fin N) :
    (canonicalCompletedC3AmbientRadialTiltPoint k N n).re = 0 := by
  simp [canonicalCompletedC3AmbientRadialTiltPoint,
    canonicalCompletedC3AmbientRadialTiltStep]

@[simp] theorem canonicalCompletedC3AmbientRadialTiltPoint_im
    (k N : ℕ) (n : Fin N) :
    (canonicalCompletedC3AmbientRadialTiltPoint k N n).im =
      (((n : ℕ) + 1 : ℕ) : ℝ) *
        canonicalCompletedC3AmbientRadialTiltScale k N := by
  simp [canonicalCompletedC3AmbientRadialTiltPoint,
    canonicalCompletedC3AmbientRadialTiltStep]

theorem canonicalCompletedC3AmbientRadialTiltPoint_im_pos
    (k N : ℕ) (n : Fin N) :
    0 < (canonicalCompletedC3AmbientRadialTiltPoint k N n).im := by
  rw [canonicalCompletedC3AmbientRadialTiltPoint_im]
  rw [canonicalCompletedC3AmbientRadialTiltScale]
  positivity

theorem canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero
    (k N : ℕ) (n : Fin N) :
    (canonicalCompletedC3AmbientRadialTiltPoint k N n).im ≠ 0 :=
  ne_of_gt (canonicalCompletedC3AmbientRadialTiltPoint_im_pos k N n)

/-- Every fixed point of the admissible finite grid approaches the Taylor
center as the radial cutoff grows. -/
theorem canonicalCompletedC3AmbientRadialTiltPoint_tendsto_zero
    (N : ℕ) (n : Fin N) :
    Tendsto (fun k : ℕ =>
      canonicalCompletedC3AmbientRadialTiltPoint k N n)
      atTop (nhds 0) := by
  let coefficient : ℂ :=
    ((((n : ℕ) + 1 : ℕ) : ℂ) * Complex.I) *
      (((2 * (N + 1) : ℕ) : ℂ)⁻¹)
  have hlimit := canonicalGreenJetStep_tendsto_zero.const_mul coefficient
  convert hlimit using 1
  · funext k
    unfold canonicalCompletedC3AmbientRadialTiltPoint
      canonicalCompletedC3AmbientRadialTiltStep
      canonicalCompletedC3AmbientRadialTiltScale
      canonicalGreenJetStep coefficient
    push_cast
    field_simp
  · simp

/-- Every point of the finite grid lies in the positive half-plane required
by the completed C3 ambient response. -/
theorem canonicalCompletedC3AmbientRadialTiltPoint_half_pos
    (k N : ℕ) (n : Fin N) :
    0 < (operatorHeightParameter
      (canonicalCompletedC3AmbientRadialTiltPoint k N n)).re := by
  rw [show (operatorHeightParameter
      (canonicalCompletedC3AmbientRadialTiltPoint k N n)).re =
        (1 / 2 : ℝ) -
          (canonicalCompletedC3AmbientRadialTiltPoint k N n).im by
    norm_num [operatorHeightParameter]
    ring]
  rw [canonicalCompletedC3AmbientRadialTiltPoint_im]
  have hn : ((n : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by
    have hnNat : (n : ℕ) + 1 ≤ N := Nat.succ_le_iff.mpr n.isLt
    exact_mod_cast hnNat
  have hk : (0 : ℝ) ≤ k := by positivity
  have hN : (0 : ℝ) ≤ N := by positivity
  have hden : (0 : ℝ) < ((2 * (N + 1) * (k + 1) : ℕ) : ℝ) := by
    positivity
  rw [canonicalCompletedC3AmbientRadialTiltScale]
  rw [show (((n : ℕ) + 1 : ℕ) : ℝ) *
      ((2 * (N + 1) * (k + 1) : ℕ) : ℝ)⁻¹ =
        (((n : ℕ) + 1 : ℕ) : ℝ) /
          ((2 * (N + 1) * (k + 1) : ℕ) : ℝ) by
      rw [div_eq_mul_inv]]
  rw [sub_pos, div_lt_iff₀ hden]
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  have hNk : 0 ≤ (N : ℝ) * (k : ℝ) := mul_nonneg hN hk
  calc
    ((n : ℕ) : ℝ) + 1 ≤ (N : ℝ) := hn
    _ < ((N : ℝ) + 1) * ((k : ℝ) + 1) := by nlinarith
    _ = (1 / 2 : ℝ) * (2 * ((N : ℝ) + 1) * ((k : ℝ) + 1)) := by ring

/-- The admissible radial grid lies in the full open critical strip, not only
in the positive half-plane used by the source construction. -/
theorem canonicalCompletedC3AmbientRadialTiltPoint_mem_genuineCriticalStrip
    (k N : ℕ) (n : Fin N) :
    operatorHeightParameter
        (canonicalCompletedC3AmbientRadialTiltPoint k N n) ∈
      CPFormal.Analytic.Cp.genuineCriticalStrip := by
  constructor
  · exact canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N n
  · rw [show (operatorHeightParameter
        (canonicalCompletedC3AmbientRadialTiltPoint k N n)).re =
          (1 / 2 : ℝ) -
            (canonicalCompletedC3AmbientRadialTiltPoint k N n).im by
      norm_num [operatorHeightParameter]
      ring]
    have him := canonicalCompletedC3AmbientRadialTiltPoint_im_pos k N n
    linarith

/-- Camera `3` is used only to read the already camera-independent compressed
source limit. -/
private theorem canonicalCompletedC3AmbientRadial_cameraThree_supported :
    FiniteNativeCarryOperator.Camera.IsSupported 3 := by
  norm_num [FiniteNativeCarryOperator.Camera.IsSupported]

/-- The bounded source-form witness supplied unconditionally by the strong
cutoff tail estimate, specialized to one radial sample. -/
theorem canonicalCompletedC3AmbientRadialCompressedSourceBound
    (k N : ℕ) (n : Fin N) :
    CanonicalCompletedC3CompressedSourceFormBounded
      (canonicalCompletedC3AmbientRadialTiltPoint k N n)
      (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N n) :=
  Classical.choose
    (exists_canonicalCompletedC3CompressedHilbertSource_tendsto
      canonicalCompletedC3AmbientRadial_cameraThree_supported
      (canonicalCompletedC3AmbientRadialTiltPoint k N n)
      (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N n))

/-- The chosen radial Riesz source is exactly the strong limit of the finite
causal compressed sources. -/
theorem canonicalCompletedC3AmbientRadialCompressedSource_tendsto
    (k N : ℕ) (n : Fin N) :
    Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          canonicalCompletedC3AmbientRadial_cameraThree_supported cutoff
          (canonicalCompletedC3AmbientRadialTiltPoint k N n))
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource
        (canonicalCompletedC3AmbientRadialTiltPoint k N n)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N n)
        (canonicalCompletedC3AmbientRadialCompressedSourceBound k N n))) :=
  Classical.choose_spec
    (exists_canonicalCompletedC3CompressedHilbertSource_tendsto
      canonicalCompletedC3AmbientRadial_cameraThree_supported
      (canonicalCompletedC3AmbientRadialTiltPoint k N n)
      (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N n))

/-- The four source-matched channels left after the independently proved
invisibility of the source leak. -/
def canonicalCompletedC3AmbientRadialWronskianCorrectionLedger
    (k N : ℕ) (i j : Fin N) : ℂ :=
  let z := canonicalCompletedC3AmbientRadialTiltPoint k N i
  let w := canonicalCompletedC3AmbientRadialTiltPoint k N j
  let hz := canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k N i
  let hw := canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k N j
  let hzHalf := canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i
  let hwHalf := canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N j
  let hzBound := canonicalCompletedC3AmbientRadialCompressedSourceBound k N i
  let hwBound := canonicalCompletedC3AmbientRadialCompressedSourceBound k N j
  canonicalCompletedC3RawGammaWronskianDefect z w hz hw +
    canonicalCompletedC3CompressedTfvdPortResolvedCorrectionBoundaryReadout
      z w hz hw hzHalf hwHalf hzBound hwBound +
    canonicalCompletedC3AmbientLeakResolvedCorrectionBoundaryReadout
      z w hz hw hzHalf hwHalf hzBound hwBound +
    canonicalCompletedC3CompressedTfvdPortSourceCorrectionBoundaryReadout
      z w hzHalf hwHalf hzBound hwBound

/-- Exact radial specialization of the full ambient/Wronskian square.  No
source bound, convergence premise, or scalar no-leak premise remains in the
interface: each is discharged by the completed causal tail theorem. -/
theorem canonicalCompletedC3AmbientRadialBoundary_sub_wronskian_eq_ledger
    (M k N : ℕ) (i j : Fin N) :
    canonicalCompletedC3AmbientBoundaryReadout
          (canonicalCompletedC3AmbientRadialTiltPoint k N i)
          (canonicalCompletedC3AmbientRadialTiltPoint k N j)
          (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i)
          (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N j) -
        canonicalC3BracketTfvdCompletedWronskianReadout M
          (canonicalCompletedC3AmbientRadialTiltPoint k N j)
          (canonicalCompletedC3AmbientRadialTiltPoint k N i) =
      canonicalCompletedC3AmbientRadialWronskianCorrectionLedger k N i j := by
  exact canonicalCompletedC3AmbientBoundary_sub_tfvdWronskian_eq_fourChannels
    canonicalCompletedC3AmbientRadial_cameraThree_supported M
    (canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k N i)
    (canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k N j)
    (canonicalCompletedC3AmbientRadialTiltPoint_mem_genuineCriticalStrip k N i)
    (canonicalCompletedC3AmbientRadialTiltPoint_mem_genuineCriticalStrip k N j)
    (canonicalCompletedC3AmbientRadialCompressedSourceBound k N i)
    (canonicalCompletedC3AmbientRadialCompressedSourceBound k N j)
    (canonicalCompletedC3AmbientRadialCompressedSource_tendsto k N i)
    (canonicalCompletedC3AmbientRadialCompressedSource_tendsto k N j)

/-- Gram matrix of the actual completed ambient causal responses on the
finite radial grid. -/
def canonicalCompletedC3AmbientRadialResponseSampleMatrix
    (k N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    canonicalCompletedC3AmbientResponseKernel
      (canonicalCompletedC3AmbientRadialTiltPoint k N i)
      (canonicalCompletedC3AmbientRadialTiltPoint k N j)
      (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i)
      (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N j)

/-- Positivity now belongs to the source-matched all-cutoff carrier, rather
than to the separately packed static Gamma source. -/
theorem canonicalCompletedC3AmbientRadialResponseSampleMatrix_posSemidef
    (k N : ℕ) :
    (canonicalCompletedC3AmbientRadialResponseSampleMatrix k N).PosSemidef := by
  simpa [canonicalCompletedC3AmbientRadialResponseSampleMatrix] using
    (canonicalCompletedC3AmbientResponseKernel_posSemidef
      (point := canonicalCompletedC3AmbientRadialTiltPoint k N)
      (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N))

/-- Matrix of the full response-source boundary skew on the same grid. -/
def canonicalCompletedC3AmbientRadialBoundarySampleMatrix
    (k N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    canonicalCompletedC3AmbientBoundaryReadout
      (canonicalCompletedC3AmbientRadialTiltPoint k N i)
      (canonicalCompletedC3AmbientRadialTiltPoint k N j)
      (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i)
      (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N j)

/-- Exact division-free Green identity for every entry of the source-matched
ambient radial matrix. -/
theorem canonicalCompletedC3AmbientRadialBoundarySampleMatrix_apply
    (k N : ℕ) (i j : Fin N) :
    canonicalCompletedC3AmbientRadialBoundarySampleMatrix k N i j =
      (canonicalCompletedC3AmbientRadialTiltPoint k N j -
          conj (canonicalCompletedC3AmbientRadialTiltPoint k N i)) *
        canonicalCompletedC3AmbientRadialResponseSampleMatrix k N i j := by
  exact canonicalCompletedC3AmbientBoundaryReadout_eq_kernel
    (canonicalCompletedC3AmbientRadialTiltPoint k N i)
    (canonicalCompletedC3AmbientRadialTiltPoint k N j)
    (canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k N i)
    (canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k N j)
    (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i)
    (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N j)

/-! ## Exact characteristic normalization -/

/-- Full ambient response with the same `sqrt 2 * F` normalization used by
the completed-native logarithmic response. -/
def canonicalCompletedC3NormalizedAmbientResponseState
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re) :
    CarryGammaComplexNaimark :=
  ((((Real.sqrt 2 : ℝ) : ℂ) *
      completedNativeOperatorCharacteristic z)⁻¹) •
    canonicalCompletedC3AmbientResponseState z hzHalf

/-- Normalized positive kernel of the source-matched ambient responses. -/
def canonicalCompletedC3NormalizedAmbientResponseKernel
    (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  canonicalCompletedC3AmbientResponseKernel z w hzHalf hwHalf /
    canonicalCompletedC3GammaCharacteristicWeight z w

/-- The quotient normalization is exactly the Gram of the normalized ambient
states.  This uses the canonical characteristic weight, not an adjusted
constant. -/
theorem canonicalCompletedC3NormalizedAmbientResponseKernel_eq_inner
    (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3NormalizedAmbientResponseKernel
        z w hzHalf hwHalf =
      inner ℂ
        (canonicalCompletedC3NormalizedAmbientResponseState z hzHalf)
        (canonicalCompletedC3NormalizedAmbientResponseState w hwHalf) := by
  unfold canonicalCompletedC3NormalizedAmbientResponseKernel
    canonicalCompletedC3GammaCharacteristicWeight
    canonicalCompletedC3NormalizedAmbientResponseState
    canonicalCompletedC3AmbientResponseKernel
  have hsqrt_sq : (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hsqrt_inv_sq : (2 : ℂ)⁻¹ =
      ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
        ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    rw [← hsqrt_sq, ← inv_pow, pow_two]
  rw [inner_smul_left, inner_smul_right]
  simp only [map_inv₀, map_mul, Complex.conj_ofReal]
  simp only [div_eq_mul_inv, mul_inv]
  rw [hsqrt_inv_sq]
  ring

/-- Every finite section of the normalized full ambient kernel remains PSD,
including under Lean's total inverse at characteristic zeros. -/
theorem canonicalCompletedC3NormalizedAmbientResponseKernel_posSemidef
    {ι : Type*} [Finite ι]
    (point : ι → ℂ)
    (hhalf : ∀ i, 0 < (operatorHeightParameter (point i)).re) :
    (Matrix.of fun i j =>
      canonicalCompletedC3NormalizedAmbientResponseKernel
        (point i) (point j) (hhalf i) (hhalf j)).PosSemidef := by
  rw [show (Matrix.of fun i j =>
      canonicalCompletedC3NormalizedAmbientResponseKernel
        (point i) (point j) (hhalf i) (hhalf j)) =
      Matrix.gram ℂ (fun i =>
        canonicalCompletedC3NormalizedAmbientResponseState
          (point i) (hhalf i)) by
    ext i j
    exact canonicalCompletedC3NormalizedAmbientResponseKernel_eq_inner
      (point i) (point j) (hhalf i) (hhalf j)]
  exact Matrix.posSemidef_gram ℂ _

/-- Full ambient source-response boundary with the same characteristic
normalization as its positive Gram. -/
def canonicalCompletedC3NormalizedAmbientBoundaryReadout
    (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  canonicalCompletedC3AmbientBoundaryReadout z w hzHalf hwHalf /
    canonicalCompletedC3GammaCharacteristicWeight z w

/-- Exact normalized Green identity for the actual all-cutoff causal source. -/
theorem canonicalCompletedC3NormalizedAmbientBoundaryReadout_eq_kernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3NormalizedAmbientBoundaryReadout
        z w hzHalf hwHalf =
      (w - conj z) *
        canonicalCompletedC3NormalizedAmbientResponseKernel
          z w hzHalf hwHalf := by
  rw [canonicalCompletedC3NormalizedAmbientBoundaryReadout,
    canonicalCompletedC3NormalizedAmbientResponseKernel,
    canonicalCompletedC3AmbientBoundaryReadout_eq_kernel
      z w hz hw hzHalf hwHalf]
  unfold canonicalCompletedC3AmbientResponseKernel
    canonicalCompletedC3AmbientResponseState
  ring

theorem canonicalCompletedC3AmbientRadialTilt_separation_ne_zero
    (k N : ℕ) (i j : Fin N) :
    canonicalCompletedC3AmbientRadialTiltPoint k N j -
        conj (canonicalCompletedC3AmbientRadialTiltPoint k N i) ≠ 0 := by
  intro hzero
  have him := congrArg Complex.im hzero
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at him
  have hi := canonicalCompletedC3AmbientRadialTiltPoint_im_pos k N i
  have hj := canonicalCompletedC3AmbientRadialTiltPoint_im_pos k N j
  linarith

/-- Completed-native polarized `dslope` sampled on the same admissible grid. -/
def canonicalCompletedNativeAmbientRadialDslopeSampleMatrix
    (k N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    canonicalCompletedNativePolarizedDslopeKernel
      (canonicalCompletedC3AmbientRadialTiltPoint k N i)
      (canonicalCompletedC3AmbientRadialTiltPoint k N j)

/-- Normalized ambient Gram on the admissible radial grid. -/
def canonicalCompletedC3NormalizedAmbientRadialResponseSampleMatrix
    (k N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    canonicalCompletedC3NormalizedAmbientResponseKernel
      (canonicalCompletedC3AmbientRadialTiltPoint k N i)
      (canonicalCompletedC3AmbientRadialTiltPoint k N j)
      (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i)
      (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N j)

theorem
    canonicalCompletedC3NormalizedAmbientRadialResponseSampleMatrix_posSemidef
    (k N : ℕ) :
    (canonicalCompletedC3NormalizedAmbientRadialResponseSampleMatrix
      k N).PosSemidef := by
  simpa [canonicalCompletedC3NormalizedAmbientRadialResponseSampleMatrix] using
    (canonicalCompletedC3NormalizedAmbientResponseKernel_posSemidef
      (point := canonicalCompletedC3AmbientRadialTiltPoint k N)
      (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N))

/-- Normalized ambient boundary matrix on the same grid. -/
def canonicalCompletedC3NormalizedAmbientRadialBoundarySampleMatrix
    (k N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    canonicalCompletedC3NormalizedAmbientBoundaryReadout
      (canonicalCompletedC3AmbientRadialTiltPoint k N i)
      (canonicalCompletedC3AmbientRadialTiltPoint k N j)
      (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i)
      (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N j)

theorem canonicalCompletedC3NormalizedAmbientRadialBoundarySampleMatrix_apply
    (k N : ℕ) (i j : Fin N) :
    canonicalCompletedC3NormalizedAmbientRadialBoundarySampleMatrix k N i j =
      (canonicalCompletedC3AmbientRadialTiltPoint k N j -
          conj (canonicalCompletedC3AmbientRadialTiltPoint k N i)) *
        canonicalCompletedC3NormalizedAmbientRadialResponseSampleMatrix
          k N i j := by
  exact canonicalCompletedC3NormalizedAmbientBoundaryReadout_eq_kernel
    (canonicalCompletedC3AmbientRadialTiltPoint k N i)
    (canonicalCompletedC3AmbientRadialTiltPoint k N j)
    (canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k N i)
    (canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k N j)
    (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i)
    (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N j)

/-- The completed TFVD Wronskian, divided by its exact characteristic weight,
is the normalized-response numerator and hence separation times `dslope`. -/
theorem canonicalC3BracketTfvdCompletedWronskianReadout_div_weight_eq_mul_dslope
    (M : ℕ) {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈
      CPFormal.Analytic.Cp.genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈
      CPFormal.Analytic.Cp.genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalC3BracketTfvdCompletedWronskianReadout M w z /
        canonicalCompletedC3GammaCharacteristicWeight z w =
      (w - conj z) *
        canonicalCompletedNativePolarizedDslopeKernel z w := by
  have hcompanion :
      (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u) =
        completedNativeOperatorBoundaryCompanion := by
    funext u
    exact (completedNativeOperatorBoundaryCompanion_eq_neg_deriv u).symm
  calc
    canonicalC3BracketTfvdCompletedWronskianReadout M w z /
          canonicalCompletedC3GammaCharacteristicWeight z w =
        completedGreenWronskian
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion w z /
          canonicalCompletedC3GammaCharacteristicWeight z w := by
      rw [canonicalC3BracketTfvdCompletedWronskianReadout_eq_F_negFprime
        M hwStrip hzStrip, hcompanion]
    _ = canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M z w :=
      (canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_eq_wronskian_div_weight
        M hzStrip hwStrip hzF hwF).symm
    _ = (w - conj z) *
          canonicalCompletedNativePolarizedDslopeKernel z w :=
      canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_eq_mul_dslope
        M hzStrip hwStrip hzF hwF hsep

/-- The corrected source-matched radial sewing gate.  Both sides now use the
canonical `sqrt 2 * F` normalization. -/
def CanonicalCompletedC3NormalizedAmbientRadialTiltBoundaryIntertwining : Prop :=
  ∀ k N (i j : Fin N),
    canonicalCompletedC3NormalizedAmbientRadialBoundarySampleMatrix k N i j =
      (canonicalCompletedC3AmbientRadialTiltPoint k N j -
          conj (canonicalCompletedC3AmbientRadialTiltPoint k N i)) *
        canonicalCompletedNativeAmbientRadialDslopeSampleMatrix k N i j

/-- Raw, stronger comparison retained for compatibility.  The canonical HP
gate is the normalized version below. -/
def CanonicalCompletedC3AmbientRadialTiltBoundaryIntertwining : Prop :=
  ∀ k N (i j : Fin N),
    canonicalCompletedC3AmbientRadialBoundarySampleMatrix k N i j =
      (canonicalCompletedC3AmbientRadialTiltPoint k N j -
          conj (canonicalCompletedC3AmbientRadialTiltPoint k N i)) *
        canonicalCompletedNativeAmbientRadialDslopeSampleMatrix k N i j

/-- The normalized source-matched boundary intertwining identifies the two
finite kernels entry by entry. -/
theorem canonicalCompletedC3NormalizedAmbientRadialResponseSampleMatrix_eq_dslope
    (hboundary :
      CanonicalCompletedC3NormalizedAmbientRadialTiltBoundaryIntertwining)
    (k N : ℕ) :
    canonicalCompletedC3NormalizedAmbientRadialResponseSampleMatrix k N =
      canonicalCompletedNativeAmbientRadialDslopeSampleMatrix k N := by
  ext i j
  have hgreen :=
    canonicalCompletedC3NormalizedAmbientRadialBoundarySampleMatrix_apply
      k N i j
  have hsew := hboundary k N i j
  rw [hgreen] at hsew
  exact mul_left_cancel₀
    (canonicalCompletedC3AmbientRadialTilt_separation_ne_zero k N i j) hsew

/-- Consequently the completed-native samples inherit PSD from the actual
causal all-cutoff response as soon as the one remaining boundary identity is
proved. -/
theorem canonicalCompletedNativeAmbientRadialDslopeSampleMatrix_posSemidef
    (hboundary :
      CanonicalCompletedC3NormalizedAmbientRadialTiltBoundaryIntertwining)
    (k N : ℕ) :
    (canonicalCompletedNativeAmbientRadialDslopeSampleMatrix k N).PosSemidef := by
  rw [← canonicalCompletedC3NormalizedAmbientRadialResponseSampleMatrix_eq_dslope
    hboundary k N]
  exact
    canonicalCompletedC3NormalizedAmbientRadialResponseSampleMatrix_posSemidef
      k N

/-- Exact normalized form of the four-channel radial ledger.  Thus the
remaining source-matched sewing is equivalent to the vanishing of this whole
ledger after canonical normalization; no individual channel is erased. -/
theorem
    canonicalCompletedC3NormalizedAmbientRadialBoundary_sub_dslope_eq_ledger
    (M k N : ℕ) (i j : Fin N)
    (hiF : completedNativeOperatorCharacteristic
      (canonicalCompletedC3AmbientRadialTiltPoint k N i) ≠ 0)
    (hjF : completedNativeOperatorCharacteristic
      (canonicalCompletedC3AmbientRadialTiltPoint k N j) ≠ 0) :
    canonicalCompletedC3NormalizedAmbientRadialBoundarySampleMatrix k N i j -
        (canonicalCompletedC3AmbientRadialTiltPoint k N j -
          conj (canonicalCompletedC3AmbientRadialTiltPoint k N i)) *
          canonicalCompletedNativeAmbientRadialDslopeSampleMatrix k N i j =
      canonicalCompletedC3AmbientRadialWronskianCorrectionLedger k N i j /
        canonicalCompletedC3GammaCharacteristicWeight
          (canonicalCompletedC3AmbientRadialTiltPoint k N i)
          (canonicalCompletedC3AmbientRadialTiltPoint k N j) := by
  let z := canonicalCompletedC3AmbientRadialTiltPoint k N i
  let w := canonicalCompletedC3AmbientRadialTiltPoint k N j
  have hsep : w ≠ conj z := by
    exact sub_ne_zero.mp
      (canonicalCompletedC3AmbientRadialTilt_separation_ne_zero k N i j)
  have hwron :=
    canonicalC3BracketTfvdCompletedWronskianReadout_div_weight_eq_mul_dslope
      M
      (canonicalCompletedC3AmbientRadialTiltPoint_mem_genuineCriticalStrip
        k N i)
      (canonicalCompletedC3AmbientRadialTiltPoint_mem_genuineCriticalStrip
        k N j)
      hiF hjF hsep
  have hledger :=
    canonicalCompletedC3AmbientRadialBoundary_sub_wronskian_eq_ledger
      M k N i j
  change canonicalCompletedC3AmbientBoundaryReadout z w
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N j) /
          canonicalCompletedC3GammaCharacteristicWeight z w -
      (w - conj z) * canonicalCompletedNativePolarizedDslopeKernel z w = _
  rw [← hwron, ← sub_div, hledger]

/-- Along every fixed finite radial coordinate, the completed characteristic
is eventually nonzero because the grid converges to its nonzero Taylor
center. -/
theorem
    canonicalCompletedC3AmbientRadialTiltPoint_eventually_characteristic_ne_zero
    (N : ℕ) (n : Fin N) :
    ∀ᶠ k : ℕ in atTop,
      completedNativeOperatorCharacteristic
        (canonicalCompletedC3AmbientRadialTiltPoint k N n) ≠ 0 := by
  exact (canonicalCompletedC3AmbientRadialTiltPoint_tendsto_zero N n).eventually
    (completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
      completedNativeOperatorCharacteristic_zero_ne_zero)

/-- Normalized ambient-versus-`dslope` defect on one radial entry. -/
def canonicalCompletedC3NormalizedAmbientRadialDslopeDefect
    (k N : ℕ) (i j : Fin N) : ℂ :=
  canonicalCompletedC3NormalizedAmbientRadialBoundarySampleMatrix k N i j -
    (canonicalCompletedC3AmbientRadialTiltPoint k N j -
      conj (canonicalCompletedC3AmbientRadialTiltPoint k N i)) *
      canonicalCompletedNativeAmbientRadialDslopeSampleMatrix k N i j

/-- The four-channel ledger with exactly the completed characteristic
normalization used by the ambient response state. -/
def canonicalCompletedC3NormalizedAmbientRadialCorrectionLedger
    (k N : ℕ) (i j : Fin N) : ℂ :=
  canonicalCompletedC3AmbientRadialWronskianCorrectionLedger k N i j /
    canonicalCompletedC3GammaCharacteristicWeight
      (canonicalCompletedC3AmbientRadialTiltPoint k N i)
      (canonicalCompletedC3AmbientRadialTiltPoint k N j)

/-- The normalized sewing defect is eventually literally the normalized
four-channel correction ledger.  No nonvanishing premise remains in the
statement. -/
theorem
    canonicalCompletedC3NormalizedAmbientRadialDslopeDefect_eventually_eq_ledger
    (M N : ℕ) (i j : Fin N) :
    (fun k : ℕ =>
      canonicalCompletedC3NormalizedAmbientRadialDslopeDefect k N i j) =ᶠ[atTop]
      (fun k : ℕ =>
        canonicalCompletedC3NormalizedAmbientRadialCorrectionLedger k N i j) := by
  filter_upwards
    [canonicalCompletedC3AmbientRadialTiltPoint_eventually_characteristic_ne_zero
      N i,
     canonicalCompletedC3AmbientRadialTiltPoint_eventually_characteristic_ne_zero
      N j] with k hiF hjF
  exact canonicalCompletedC3NormalizedAmbientRadialBoundary_sub_dslope_eq_ledger
    M k N i j hiF hjF

/-- Exact limit formulation of the corrected gate: asymptotic ambient
sewing is equivalent to disappearance of the complete normalized correction
ledger, rather than to disappearance of any selected channel. -/
theorem
    canonicalCompletedC3NormalizedAmbientRadialDslopeDefect_tendsto_zero_iff_ledger
    (M N : ℕ) (i j : Fin N) :
    Tendsto
        (fun k : ℕ =>
          canonicalCompletedC3NormalizedAmbientRadialDslopeDefect k N i j)
        atTop (nhds 0) ↔
      Tendsto
        (fun k : ℕ =>
          canonicalCompletedC3NormalizedAmbientRadialCorrectionLedger k N i j)
        atTop (nhds 0) := by
  constructor <;> intro h
  · exact h.congr'
      (canonicalCompletedC3NormalizedAmbientRadialDslopeDefect_eventually_eq_ledger
        M N i j)
  · exact h.congr'
      (canonicalCompletedC3NormalizedAmbientRadialDslopeDefect_eventually_eq_ledger
        M N i j).symm

end

end CarrySelfAdjointOperator
