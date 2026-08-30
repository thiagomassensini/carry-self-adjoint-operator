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

/-- Source-matched form of the remaining radial sewing gate.  It compares the
full ambient response boundary, not the boundary of the static six-camera
Gamma packing, with the completed-native normalized-response numerator. -/
def CanonicalCompletedC3AmbientRadialTiltBoundaryIntertwining : Prop :=
  ∀ k N (i j : Fin N),
    canonicalCompletedC3AmbientRadialBoundarySampleMatrix k N i j =
      (canonicalCompletedC3AmbientRadialTiltPoint k N j -
          conj (canonicalCompletedC3AmbientRadialTiltPoint k N i)) *
        canonicalCompletedNativeAmbientRadialDslopeSampleMatrix k N i j

/-- The source-matched boundary intertwining identifies the two finite
kernels entry by entry; cancellation is legitimate because the radial
separation never vanishes. -/
theorem canonicalCompletedC3AmbientRadialResponseSampleMatrix_eq_dslope
    (hboundary : CanonicalCompletedC3AmbientRadialTiltBoundaryIntertwining)
    (k N : ℕ) :
    canonicalCompletedC3AmbientRadialResponseSampleMatrix k N =
      canonicalCompletedNativeAmbientRadialDslopeSampleMatrix k N := by
  ext i j
  have hgreen :=
    canonicalCompletedC3AmbientRadialBoundarySampleMatrix_apply k N i j
  have hsew := hboundary k N i j
  rw [hgreen] at hsew
  exact mul_left_cancel₀
    (canonicalCompletedC3AmbientRadialTilt_separation_ne_zero k N i j) hsew

/-- Consequently the completed-native samples inherit PSD from the actual
causal all-cutoff response as soon as the one remaining boundary identity is
proved. -/
theorem canonicalCompletedNativeAmbientRadialDslopeSampleMatrix_posSemidef
    (hboundary : CanonicalCompletedC3AmbientRadialTiltBoundaryIntertwining)
    (k N : ℕ) :
    (canonicalCompletedNativeAmbientRadialDslopeSampleMatrix k N).PosSemidef := by
  rw [← canonicalCompletedC3AmbientRadialResponseSampleMatrix_eq_dslope
    hboundary k N]
  exact canonicalCompletedC3AmbientRadialResponseSampleMatrix_posSemidef k N

end

end CarrySelfAdjointOperator
