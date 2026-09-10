import CarrySelfAdjointOperator.AtlasEnergySixCameraHilbertAsymptoticCrosswalk
import CarrySelfAdjointOperator.FiniteEnrichedCameraState
import CarrySelfAdjointOperator.MultibaseTfvdCameraGramHilbertTransport
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

open scoped BigOperators Matrix RealInnerProductSpace MatrixOrder
open Filter Topology

namespace CarrySelfAdjointOperator

open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- The normalised finite six-camera Gram is positive semidefinite at every
cutoff.  This is the order-theoretic input available without any continuity
claim for the matrix square-root. -/
theorem atlasNormalizedFiniteSixCameraRowGram_posSemidef
    (cutoff : ℕ) :
    (atlasNormalizedFiniteSixCameraRowGram cutoff).PosSemidef := by
  by_cases hcut : cutoff = 0
  · subst hcut
    simp [atlasNormalizedFiniteSixCameraRowGram,
      atlasRawFiniteSixCameraRowGram]
    exact Matrix.PosSemidef.zero
  · have hG :
        (finiteCameraRowGram (finiteLiteralSixCameraMatrix cutoff)).PosSemidef := by
      simpa [finiteCameraRowGram] using
        (Matrix.posSemidef_self_mul_conjTranspose
          (finiteLiteralSixCameraMatrix cutoff))
    have hscale : 0 ≤ (cutoff : ℝ)⁻¹ :=
      inv_nonneg.mpr (Nat.cast_nonneg cutoff)
    exact Matrix.PosSemidef.smul hG hscale

/-- Matrix inversion is continuous at the positive inverse square root of the
limiting six-camera Gram.  The proof uses only finite-dimensional determinant
inversion; it deliberately does not assert continuity of `CFC.sqrt` on the
matrix type. -/
theorem atlasSixCameraPositiveInverseSqrt_continuousAt :
    ContinuousAt
      (fun A : Matrix (Fin 6) (Fin 6) ℝ => A⁻¹)
      (CFC.sqrt sixCameraGram) := by
  have hspos := sixCameraGram_posDef.isStrictlyPositive.sqrt sixCameraGram
  have hunit : IsUnit (CFC.sqrt sixCameraGram) := hspos.isUnit
  have hdet : IsUnit (CFC.sqrt sixCameraGram).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hne : (CFC.sqrt sixCameraGram).det ≠ 0 := hdet.ne_zero
  have hscalar :
      ContinuousAt (fun x : ℝ => Ring.inverse x)
        ((CFC.sqrt sixCameraGram).det) := by
    simpa only [Ring.inverse_eq_inv] using (continuousAt_inv₀ hne)
  exact continuousAt_matrix_inv (CFC.sqrt sixCameraGram) hscalar

/-- The finite whitening limit follows from a square-root limit.  This is the
exact remaining topological seam in the current pin: `CFC.continuousOn_sqrt`
requires a normed-ring structure that is not available for `Matrix (Fin 6)
(Fin 6) ℝ`. -/
theorem atlasSixCameraWhiteningMatrix_tendsto_of_sqrt_tendsto
    (hS :
      Tendsto
        (fun cutoff : ℕ =>
          CFC.sqrt (atlasNormalizedFiniteSixCameraRowGram cutoff))
        atTop (nhds (CFC.sqrt sixCameraGram))) :
    Tendsto atlasSixCameraWhiteningMatrix atTop
      (nhds (positiveInverseSqrt sixCameraGram)) := by
  have hinv := atlasSixCameraPositiveInverseSqrt_continuousAt.tendsto.comp hS
  change Tendsto
    (fun cutoff : ℕ =>
      (CFC.sqrt (atlasNormalizedFiniteSixCameraRowGram cutoff))⁻¹)
    atTop (nhds (CFC.sqrt sixCameraGram)⁻¹)
  exact hinv

/-- Conditional asymptotic isometry with the order-theoretic hypotheses made
explicit. -/
theorem atlasSixCameraWhitenedHilbertEmbedding_inner_tendsto_of_sqrt_tendsto
    (hS :
      Tendsto
        (fun cutoff : ℕ =>
          CFC.sqrt (atlasNormalizedFiniteSixCameraRowGram cutoff))
        atTop (nhds (CFC.sqrt sixCameraGram)))
    (c d : Fin 6 → ℝ) :
    Tendsto
      (fun cutoff : ℕ =>
        inner ℝ
          (atlasSixCameraWhitenedHilbertEmbedding cutoff c)
          (atlasSixCameraWhitenedHilbertEmbedding cutoff d))
      atTop (nhds (c ⬝ᵥ d)) := by
  exact atlasSixCameraWhitenedHilbertEmbedding_inner_tendsto_of_inverseSqrt_tendsto
    (atlasSixCameraWhiteningMatrix_tendsto_of_sqrt_tendsto hS) c d

/-- Rank-one real matrix `|x⟩⟨x|`. -/
def rankOneMatrix {state : Type*} [Fintype state]
    (x : state → ℝ) : Matrix state state ℝ := Matrix.vecMulVec x x

@[simp] theorem rankOneMatrix_apply {state : Type*} [Fintype state]
    (x : state → ℝ) (i j : state) : rankOneMatrix x i j = x i * x j := by
  rfl

@[simp] theorem rankOneMatrix_transpose {state : Type*} [Fintype state]
    (x : state → ℝ) : (rankOneMatrix x)ᵀ = rankOneMatrix x := by
  ext i j
  simp only [rankOneMatrix, Matrix.transpose_apply, Matrix.vecMulVec_apply]
  ring

@[simp] theorem rankOneMatrix_mul_self {state : Type*} [Fintype state]
    (x : state → ℝ) :
    rankOneMatrix x * rankOneMatrix x =
      (x ⬝ᵥ x) • rankOneMatrix x := by
  ext i j
  simp only [rankOneMatrix, Matrix.mul_apply, Matrix.vecMulVec_apply,
    Matrix.smul_apply, dotProduct]
  simp only [smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- A unit rank-one state is an idempotent projector. -/
theorem rankOneMatrix_mul_self_of_dotProduct_eq_one
    {state : Type*} [Fintype state]
    (x : state → ℝ) (hx : x ⬝ᵥ x = 1) :
    rankOneMatrix x * rankOneMatrix x = rankOneMatrix x := by
  rw [rankOneMatrix_mul_self, hx, one_smul]

/-- Trace of a self-adjoint idempotent against a rank-one state. -/
theorem trace_projection_rankOne_eq_norm_sq
    {state : Type*} [Fintype state] [DecidableEq state]
    {P : Matrix state state ℝ}
    (hPT : Pᵀ = P) (hP2 : P * P = P) (x : state → ℝ) :
    (P * rankOneMatrix x).trace = (P *ᵥ x) ⬝ᵥ (P *ᵥ x) := by
  rw [Matrix.trace_mul_comm]
  have hmul : rankOneMatrix x * P = Matrix.vecMulVec x (Pᵀ *ᵥ x) := by
    ext i j
    simp only [rankOneMatrix, Matrix.mul_apply, Matrix.vecMulVec_apply,
      Matrix.transpose_apply, Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hmul, Matrix.trace_vecMulVec]
  have hvec : (P *ᵥ x) ᵥ* P = P *ᵥ x := by
    calc
      (P *ᵥ x) ᵥ* P = Pᵀ *ᵥ (P *ᵥ x) := by
        simpa only [Matrix.transpose_transpose] using
          (Matrix.vecMul_transpose Pᵀ (P *ᵥ x))
      _ = P *ᵥ x := by
        rw [hPT]
        rw [Matrix.mulVec_mulVec]
        rw [hP2]
  calc
    x ⬝ᵥ Pᵀ *ᵥ x = x ᵥ* Pᵀ ⬝ᵥ x := Matrix.dotProduct_mulVec x Pᵀ x
    _ = (P *ᵥ x) ⬝ᵥ x := by rw [Matrix.vecMul_transpose]
    _ = ((P *ᵥ x) ᵥ* P) ⬝ᵥ x := by rw [hvec]
    _ = (P *ᵥ x) ⬝ᵥ (P *ᵥ x) :=
      (Matrix.dotProduct_mulVec (P *ᵥ x) P x).symm

/-- Visible projector energy, scalarised as a finite Hilbert--Schmidt trace. -/
def projectorVisibleEnergy {state : Type*} [Fintype state]
    (P : Matrix state state ℝ) (x : state → ℝ) : ℝ :=
  (P * rankOneMatrix x).trace

/-- Blind projector energy, scalarised as a finite Hilbert--Schmidt trace. -/
def projectorBlindEnergy {state : Type*} [Fintype state] [DecidableEq state]
    (P : Matrix state state ℝ) (x : state → ℝ) : ℝ :=
  ((1 - P) * rankOneMatrix x).trace

@[simp] theorem projectorVisibleEnergy_eq_norm_sq
    {state : Type*} [Fintype state] [DecidableEq state]
    {P : Matrix state state ℝ}
    (hPT : Pᵀ = P) (hP2 : P * P = P) (x : state → ℝ) :
    projectorVisibleEnergy P x = (P *ᵥ x) ⬝ᵥ (P *ᵥ x) := by
  exact trace_projection_rankOne_eq_norm_sq hPT hP2 x

@[simp] theorem projectorBlindEnergy_eq_norm_sq
    {state : Type*} [Fintype state] [DecidableEq state]
    {P : Matrix state state ℝ}
    (hPT : Pᵀ = P) (hP2 : P * P = P) (x : state → ℝ) :
    projectorBlindEnergy P x = ((1 - P) *ᵥ x) ⬝ᵥ ((1 - P) *ᵥ x) := by
  unfold projectorBlindEnergy
  apply trace_projection_rankOne_eq_norm_sq
  · rw [Matrix.transpose_sub, Matrix.transpose_one, hPT]
  · calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP2]; noncomm_ring

/-- The two trace energies exactly recover the state energy. -/
theorem projector_energies_add_eq_norm_sq
    {state : Type*} [Fintype state] [DecidableEq state]
    {P : Matrix state state ℝ}
    (_hPT : Pᵀ = P) (_hP2 : P * P = P) (x : state → ℝ) :
    projectorVisibleEnergy P x + projectorBlindEnergy P x = x ⬝ᵥ x := by
  unfold projectorVisibleEnergy projectorBlindEnergy
  rw [← Matrix.trace_add]
  have hsum : P * rankOneMatrix x + (1 - P) * rankOneMatrix x =
      rankOneMatrix x := by
    rw [Matrix.sub_mul]
    simp only [Matrix.one_mul]
    abel
  rw [hsum]
  simpa only [rankOneMatrix] using (Matrix.trace_vecMulVec x x)

/-- Visible energy for the canonical finite camera projector is the squared
norm of its canonical readout. -/
theorem finiteCanonicalCameraVisibleEnergy_eq_readout_norm_sq
    {camera state : Type*}
    [Fintype camera] [DecidableEq camera]
    [Fintype state] [DecidableEq state]
    (C : Matrix camera state ℝ)
    (hG : (finiteCameraRowGram C).PosDef)
    (x : state → ℝ) :
    projectorVisibleEnergy (finiteCanonicalCameraProjection C) x =
      (finiteCanonicalCameraReadout C *ᵥ x) ⬝ᵥ
        (finiteCanonicalCameraReadout C *ᵥ x) := by
  rw [projectorVisibleEnergy_eq_norm_sq
    (finiteCanonicalCameraProjection_transpose hG)
    (finiteCanonicalCameraProjection_mul_self hG)]
  rw [finiteCanonicalCameraProjection_eq_transpose_mul hG]
  have hPx :
      ((finiteCanonicalCameraReadout C)ᵀ *
          finiteCanonicalCameraReadout C) *ᵥ x =
        (finiteCanonicalCameraReadout C)ᵀ *ᵥ
          (finiteCanonicalCameraReadout C *ᵥ x) := by
    exact (Matrix.mulVec_mulVec x
      (finiteCanonicalCameraReadout C)ᵀ
      (finiteCanonicalCameraReadout C)).symm
  rw [hPx]
  have hRR := finiteCanonicalCameraReadout_mul_transpose hG
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_transpose]
  rw [Matrix.mulVec_mulVec, hRR]
  simp

/-- Blind energy for the canonical finite camera projector is the squared norm
of the complementary blind/provenance projection. -/
theorem finiteCanonicalCameraBlindEnergy_eq_blind_norm_sq
    {camera state : Type*}
    [Fintype camera] [DecidableEq camera]
    [Fintype state] [DecidableEq state]
    (C : Matrix camera state ℝ)
    (hG : (finiteCameraRowGram C).PosDef)
    (x : state → ℝ) :
    projectorBlindEnergy (finiteCanonicalCameraProjection C) x =
      (finiteCanonicalCameraBlindProjection C *ᵥ x) ⬝ᵥ
        (finiteCanonicalCameraBlindProjection C *ᵥ x) := by
  apply projectorBlindEnergy_eq_norm_sq
  · exact finiteCanonicalCameraProjection_transpose hG
  · exact finiteCanonicalCameraProjection_mul_self hG

/-- Finite camera visible and blind energies add to the full state energy. -/
theorem finiteCanonicalCameraVisibleBlindEnergy_add_eq_state_norm_sq
    {camera state : Type*}
    [Fintype camera] [DecidableEq camera]
    [Fintype state] [DecidableEq state]
    (C : Matrix camera state ℝ)
    (hG : (finiteCameraRowGram C).PosDef)
    (x : state → ℝ) :
    projectorVisibleEnergy (finiteCanonicalCameraProjection C) x +
        projectorBlindEnergy (finiteCanonicalCameraProjection C) x =
      x ⬝ᵥ x := by
  apply projector_energies_add_eq_norm_sq
  · exact finiteCanonicalCameraProjection_transpose hG
  · exact finiteCanonicalCameraProjection_mul_self hG

/-- The preceding trace identity is the finite Hilbert--Schmidt form of the
existing enriched-camera Parseval decomposition. -/
theorem finiteCanonicalCameraVisibleBlindEnergy_eq_enriched_parseval
    {camera state : Type*}
    [Fintype camera] [DecidableEq camera]
    [Fintype state] [DecidableEq state]
    (C : Matrix camera state ℝ)
    (hG : (finiteCameraRowGram C).PosDef)
    (x : state → ℝ) :
    projectorVisibleEnergy (finiteCanonicalCameraProjection C) x +
        projectorBlindEnergy (finiteCanonicalCameraProjection C) x =
      x ⬝ᵥ x := by
  exact finiteCanonicalCameraVisibleBlindEnergy_add_eq_state_norm_sq C hG x

end
end CarrySelfAdjointOperator
