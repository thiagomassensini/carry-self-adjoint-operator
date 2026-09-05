import CarrySelfAdjointOperator.FiniteCanonicalCameraReadout

/-!
# Canonical enriched finite camera state

The canonical coisometric readout `R` retains the camera-visible part of a
finite state.  Its transpose `V = Rᵀ` synthesizes that part back into the
state space.  This file keeps the complementary blind/provenance sector
instead of discarding it.

With

`P = V R = Rᵀ R` and `B = I - P`,

the joint analysis `x |-> (R x, B x)` is Parseval:

`Rᵀ R + Bᵀ B = I`.

The final theorem shows that every value/log-jet Green commutator splits
exactly into its visible-camera and blind/provenance channels.  No section,
pseudoinverse, preferred representative, or spectral value is used.
-/

open scoped Matrix

noncomputable section

namespace NativeCarryC3Crosswalk

variable {camera state : Type*}
  [Fintype camera] [DecidableEq camera]
  [Fintype state] [DecidableEq state]

/-- Orthogonal projection onto the coherently synthesized camera sector. -/
def finiteCanonicalCameraProjection (C : Matrix camera state ℝ) :
    Matrix state state ℝ :=
  finiteCanonicalCameraSynthesis C * finiteCanonicalCameraReadout C

/-- Complementary sector retaining everything invisible to the camera
readout. -/
def finiteCanonicalCameraBlindProjection (C : Matrix camera state ℝ) :
    Matrix state state ℝ :=
  1 - finiteCanonicalCameraProjection C

omit [DecidableEq state] in
/-- The coherent projection is the Gram `Rᵀ R` of the canonical readout. -/
theorem finiteCanonicalCameraProjection_eq_transpose_mul
    {C : Matrix camera state ℝ}
    (hG : (finiteCameraRowGram C).PosDef) :
    finiteCanonicalCameraProjection C =
      (finiteCanonicalCameraReadout C)ᵀ * finiteCanonicalCameraReadout C := by
  rw [finiteCanonicalCameraProjection,
    finiteCanonicalCameraReadout_transpose hG]

omit [DecidableEq state] in
/-- The coherent camera-sector projection is self-adjoint. -/
theorem finiteCanonicalCameraProjection_transpose
    {C : Matrix camera state ℝ}
    (hG : (finiteCameraRowGram C).PosDef) :
    (finiteCanonicalCameraProjection C)ᵀ =
      finiteCanonicalCameraProjection C := by
  rw [finiteCanonicalCameraProjection_eq_transpose_mul hG,
    Matrix.transpose_mul, Matrix.transpose_transpose]

omit [DecidableEq state] in
/-- The coherent camera-sector projection is idempotent. -/
theorem finiteCanonicalCameraProjection_mul_self
    {C : Matrix camera state ℝ}
    (hG : (finiteCameraRowGram C).PosDef) :
    finiteCanonicalCameraProjection C *
        finiteCanonicalCameraProjection C =
      finiteCanonicalCameraProjection C := by
  unfold finiteCanonicalCameraProjection
  rw [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (finiteCanonicalCameraReadout C)
    (finiteCanonicalCameraSynthesis C)
    (finiteCanonicalCameraReadout C)]
  rw [finiteCanonicalCameraReadout_synthesis hG]
  simp

/-- The blind/provenance complement is self-adjoint. -/
theorem finiteCanonicalCameraBlindProjection_transpose
    {C : Matrix camera state ℝ}
    (hG : (finiteCameraRowGram C).PosDef) :
    (finiteCanonicalCameraBlindProjection C)ᵀ =
      finiteCanonicalCameraBlindProjection C := by
  rw [finiteCanonicalCameraBlindProjection, Matrix.transpose_sub,
    Matrix.transpose_one, finiteCanonicalCameraProjection_transpose hG]

/-- The blind/provenance complement is itself a projection. -/
theorem finiteCanonicalCameraBlindProjection_mul_self
    {C : Matrix camera state ℝ}
    (hG : (finiteCameraRowGram C).PosDef) :
    finiteCanonicalCameraBlindProjection C *
        finiteCanonicalCameraBlindProjection C =
      finiteCanonicalCameraBlindProjection C := by
  rw [finiteCanonicalCameraBlindProjection]
  have hP := finiteCanonicalCameraProjection_mul_self hG
  calc
    (1 - finiteCanonicalCameraProjection C) *
        (1 - finiteCanonicalCameraProjection C) =
      1 - finiteCanonicalCameraProjection C -
        finiteCanonicalCameraProjection C +
          finiteCanonicalCameraProjection C *
            finiteCanonicalCameraProjection C := by noncomm_ring
    _ = 1 - finiteCanonicalCameraProjection C := by rw [hP]; noncomm_ring

/-- Exact enriched Parseval identity.  The camera-visible channel and the
blind/provenance channel retain the full state energy together. -/
theorem finiteCanonicalEnrichedCamera_parseval
    {C : Matrix camera state ℝ}
    (hG : (finiteCameraRowGram C).PosDef) :
    (finiteCanonicalCameraReadout C)ᵀ * finiteCanonicalCameraReadout C +
        (finiteCanonicalCameraBlindProjection C)ᵀ *
          finiteCanonicalCameraBlindProjection C = 1 := by
  rw [← finiteCanonicalCameraProjection_eq_transpose_mul hG,
    finiteCanonicalCameraBlindProjection_transpose hG,
    finiteCanonicalCameraBlindProjection_mul_self hG,
    finiteCanonicalCameraBlindProjection]
  noncomm_ring

/-- Exact reconstruction through the enriched analysis.  Since `J` is
arbitrary, this applies in particular to every finite log-jet `L^k`, without
changing the camera or selecting representatives. -/
theorem finiteCanonicalEnrichedCamera_reconstruct
    {C : Matrix camera state ℝ}
    (hG : (finiteCameraRowGram C).PosDef)
    (J : Matrix state state ℝ) :
    (finiteCanonicalCameraReadout C)ᵀ *
          (finiteCanonicalCameraReadout C * J) +
        (finiteCanonicalCameraBlindProjection C)ᵀ *
          (finiteCanonicalCameraBlindProjection C * J) = J := by
  calc
    (finiteCanonicalCameraReadout C)ᵀ *
          (finiteCanonicalCameraReadout C * J) +
        (finiteCanonicalCameraBlindProjection C)ᵀ *
          (finiteCanonicalCameraBlindProjection C * J) =
      ((finiteCanonicalCameraReadout C)ᵀ *
          finiteCanonicalCameraReadout C +
        (finiteCanonicalCameraBlindProjection C)ᵀ *
          finiteCanonicalCameraBlindProjection C) * J := by
            simp only [Matrix.mul_assoc, add_mul]
    _ = J := by rw [finiteCanonicalEnrichedCamera_parseval hG]; simp

/-- Exact value/log-jet Green decomposition through the enriched analysis.
For an arbitrary finite generator `L`, its Green commutator is the sum of the
camera-visible commutator and the blind/provenance commutator. -/
theorem finiteCanonicalEnrichedCamera_greenDecomposition
    {C : Matrix camera state ℝ}
    (hG : (finiteCameraRowGram C).PosDef)
    (L : Matrix state state ℝ) :
    L - Lᵀ =
      (finiteCanonicalCameraReadout C)ᵀ *
          (finiteCanonicalCameraReadout C * L) -
        (finiteCanonicalCameraReadout C * L)ᵀ *
          finiteCanonicalCameraReadout C +
      (finiteCanonicalCameraBlindProjection C)ᵀ *
          (finiteCanonicalCameraBlindProjection C * L) -
        (finiteCanonicalCameraBlindProjection C * L)ᵀ *
          finiteCanonicalCameraBlindProjection C := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul]
  have hParseval := finiteCanonicalEnrichedCamera_parseval hG
  calc
    L - Lᵀ = 1 * L - Lᵀ * 1 := by simp
    _ = ((finiteCanonicalCameraReadout C)ᵀ *
            finiteCanonicalCameraReadout C +
          (finiteCanonicalCameraBlindProjection C)ᵀ *
            finiteCanonicalCameraBlindProjection C) * L -
        Lᵀ * ((finiteCanonicalCameraReadout C)ᵀ *
            finiteCanonicalCameraReadout C +
          (finiteCanonicalCameraBlindProjection C)ᵀ *
            finiteCanonicalCameraBlindProjection C) := by rw [hParseval]
    _ = _ := by
      simp only [add_mul, mul_add, Matrix.mul_assoc]
      abel

end NativeCarryC3Crosswalk
