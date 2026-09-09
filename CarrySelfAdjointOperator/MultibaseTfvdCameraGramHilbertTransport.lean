import CarrySelfAdjointOperator.MultibaseCameraLogTfvdChannelTransport
import CarrySelfAdjointOperator.FiniteNativeDepthRawCameraGram
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Hilbert-valued finite camera Gram transport

This module lifts a finite real camera matrix to families of vectors in an
arbitrary complex Hilbert space.  The outer index is the camera/state index;
the Hilbert-valued entry is kept intact.  In particular, no identification is
made between a camera label and the vertical/sample coordinate inside
`CarryVerticalL2`.

The raw synthesis has the induced row-Gram metric, while the existing
positive-inverse-square-root synthesis is isometric under the row-Gram
positive-definiteness hypothesis.  The final definitions specialize this
construction to the already existing camera-resolved TFVD carrier, keeping
the camera and TFVD cutoffs as separate parameters.
-/

open scoped BigOperators Matrix lp

open NativeCarryC3Crosswalk
open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Limits


namespace CarrySelfAdjointOperator

noncomputable section

abbrev FiniteHilbertFamily (ι H : Type*) := PiLp 2 (fun _ : ι => H)

def finiteHilbertMatrixSynthesis
    {input output H : Type*}
    [Fintype input] [Fintype output]
    [NormedAddCommGroup H] [Module ℂ H]
    (A : Matrix output input ℝ) :
    FiniteHilbertFamily input H →ₗ[ℂ] FiniteHilbertFamily output H :=
  { toFun := fun X =>
      WithLp.toLp (2 : ENNReal) (fun j =>
        ∑ i : input, ((A j i : ℝ) : ℂ) • X.ofLp i)
    map_add' := by
      intro X Y
      ext j
      simp [Finset.sum_add_distrib]
    map_smul' := by
      intro c X
      ext j
      change
        (∑ i : input, ((A j i : ℝ) : ℂ) • (c • X.ofLp i)) =
          c • ∑ i : input, ((A j i : ℝ) : ℂ) • X.ofLp i
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_comm] }

@[simp] theorem finiteHilbertMatrixSynthesis_apply
    {input output H : Type*}
    [Fintype input] [Fintype output]
    [NormedAddCommGroup H] [Module ℂ H]
    (A : Matrix output input ℝ) (X : FiniteHilbertFamily input H) (j : output) :
    (finiteHilbertMatrixSynthesis A X).ofLp j =
      ∑ i : input, ((A j i : ℝ) : ℂ) • X.ofLp i := by
  rfl

theorem finiteHilbertMatrixSynthesis_comp
    {input mid output H : Type*}
    [Fintype input] [Fintype mid] [Fintype output]
    [NormedAddCommGroup H] [Module ℂ H]
    (A : Matrix mid input ℝ) (B : Matrix output mid ℝ)
    (X : FiniteHilbertFamily input H) :
    finiteHilbertMatrixSynthesis B
        (finiteHilbertMatrixSynthesis A X) =
      finiteHilbertMatrixSynthesis (B * A) X := by
  apply PiLp.ext
  intro k
  change
    (∑ x : mid, ((B k x : ℝ) : ℂ) •
      (∑ i : input, ((A x i : ℝ) : ℂ) • X.ofLp i)) =
      ∑ i : input, (((B * A) k i : ℝ) : ℂ) • X.ofLp i
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_smul]
  congr 1
  rw [Matrix.mul_apply]
  push_cast
  simp

theorem finiteHilbertMatrixSynthesis_inner_gram
    {input output H : Type*}
    [Fintype input] [Fintype output]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : Matrix output input ℝ)
    (X Y : FiniteHilbertFamily input H) :
    inner ℂ (finiteHilbertMatrixSynthesis A X)
      (finiteHilbertMatrixSynthesis A Y) =
      ∑ i : input, ∑ k : input,
        (((Aᵀ * A) i k : ℝ) : ℂ) *
          inner ℂ (X.ofLp i) (Y.ofLp k) := by
  simp only [PiLp.inner_apply, finiteHilbertMatrixSynthesis_apply]
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  push_cast
  simp only [Complex.conj_ofReal]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem finiteHilbertMatrixSynthesis_one
    {input H : Type*}
    [Fintype input] [DecidableEq input]
    [NormedAddCommGroup H] [Module ℂ H]
    (X : FiniteHilbertFamily input H) :
    finiteHilbertMatrixSynthesis (1 : Matrix input input ℝ) X = X := by
  apply PiLp.ext
  intro i
  classical
  simp [finiteHilbertMatrixSynthesis_apply, Matrix.one_apply]

noncomputable def finiteCameraHilbertRawSynthesis
    {camera state H : Type*}
    [Fintype camera] [Fintype state]
    [NormedAddCommGroup H] [Module ℂ H]
    (C : Matrix camera state ℝ) :
    FiniteHilbertFamily camera H →ₗ[ℂ] FiniteHilbertFamily state H :=
  finiteHilbertMatrixSynthesis Cᵀ

theorem finiteCameraHilbertRawSynthesis_inner
    {camera state H : Type*}
    [Fintype camera] [Fintype state]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [DecidableEq camera]
    (C : Matrix camera state ℝ)
    (X Y : FiniteHilbertFamily camera H) :
    inner ℂ (finiteCameraHilbertRawSynthesis C X)
      (finiteCameraHilbertRawSynthesis C Y) =
      ∑ i : camera, ∑ j : camera,
        (((finiteCameraRowGram C i j : ℝ) : ℂ) *
          inner ℂ (X.ofLp i) (Y.ofLp j)) := by
  simpa [finiteCameraHilbertRawSynthesis, finiteCameraRowGram,
    Matrix.transpose_transpose] using
    (finiteHilbertMatrixSynthesis_inner_gram (A := Cᵀ) X Y)

noncomputable def finiteHilbertCoordinate
    {index H : Type*} [DecidableEq index]
    [NormedAddCommGroup H]
    (i : index) (x : H) : FiniteHilbertFamily index H :=
  WithLp.toLp (2 : ENNReal) (Pi.single i x : index → H)

@[simp] theorem finiteHilbertCoordinate_apply
    {index H : Type*} [DecidableEq index]
    [NormedAddCommGroup H]
    (i : index) (x : H) (j : index) :
    (finiteHilbertCoordinate i x).ofLp j = (Pi.single i x : index → H) j := by
  rfl

theorem finiteCameraHilbertRawSynthesis_single_channel
    {camera state H : Type*}
    [Fintype camera] [Fintype state]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [DecidableEq camera]
    (C : Matrix camera state ℝ) (i j : camera) (x y : H) :
    inner ℂ
        (finiteCameraHilbertRawSynthesis C (finiteHilbertCoordinate i x))
        (finiteCameraHilbertRawSynthesis C (finiteHilbertCoordinate j y)) =
      (((finiteCameraRowGram C i j : ℝ) : ℂ) * inner ℂ x y) := by
  rw [finiteCameraHilbertRawSynthesis_inner]
  simp only [finiteHilbertCoordinate, Pi.single_apply]
  have hinner (a b : camera) :
      inner ℂ (if a = i then x else 0) (if b = j then y else 0) =
        if a = i then if b = j then inner ℂ x y else 0 else 0 := by
    by_cases ha : a = i <;> by_cases hb : b = j <;> simp [ha, hb]
  simp_rw [hinner]
  simp

noncomputable def finiteCanonicalCameraHilbertSynthesis
    {camera state H : Type*}
    [Fintype camera] [Fintype state]
    [NormedAddCommGroup H] [Module ℂ H]
    [DecidableEq camera]
    (C : Matrix camera state ℝ) :
    FiniteHilbertFamily camera H →ₗ[ℂ] FiniteHilbertFamily state H :=
  finiteHilbertMatrixSynthesis (finiteCanonicalCameraSynthesis C)

noncomputable def finiteCanonicalCameraHilbertReadout
    {camera state H : Type*}
    [Fintype camera] [Fintype state]
    [NormedAddCommGroup H] [Module ℂ H]
    [DecidableEq camera]
    (C : Matrix camera state ℝ) :
    FiniteHilbertFamily state H →ₗ[ℂ] FiniteHilbertFamily camera H :=
  finiteHilbertMatrixSynthesis (finiteCanonicalCameraReadout C)

theorem finiteCanonicalCameraHilbertSynthesis_isometry
    {camera state H : Type*}
    [Fintype camera] [Fintype state]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [DecidableEq camera]
    (C : Matrix camera state ℝ)
    (hG : (finiteCameraRowGram C).PosDef)
    (X Y : FiniteHilbertFamily camera H) :
      inner ℂ (finiteCanonicalCameraHilbertSynthesis C X)
      (finiteCanonicalCameraHilbertSynthesis C Y) =
      inner ℂ X Y := by
  change inner ℂ
      (finiteHilbertMatrixSynthesis (finiteCanonicalCameraSynthesis C) X)
      (finiteHilbertMatrixSynthesis (finiteCanonicalCameraSynthesis C) Y) =
    inner ℂ X Y
  rw [finiteHilbertMatrixSynthesis_inner_gram]
  rw [finiteCanonicalCameraSynthesis_transpose_mul hG]
  have hone := finiteHilbertMatrixSynthesis_inner_gram
    (A := (1 : Matrix camera camera ℝ)) X Y
  rw [finiteHilbertMatrixSynthesis_one X,
    finiteHilbertMatrixSynthesis_one Y] at hone
  simpa [Matrix.transpose_transpose] using hone.symm

theorem finiteCanonicalCameraHilbertReadout_synthesis
    {camera state H : Type*}
    [Fintype camera] [Fintype state]
    [NormedAddCommGroup H] [Module ℂ H]
    [DecidableEq camera]
    (C : Matrix camera state ℝ)
    (hG : (finiteCameraRowGram C).PosDef)
    (X : FiniteHilbertFamily camera H) :
    finiteCanonicalCameraHilbertReadout C
        (finiteCanonicalCameraHilbertSynthesis C X) = X := by
  change finiteHilbertMatrixSynthesis (finiteCanonicalCameraReadout C)
      (finiteHilbertMatrixSynthesis (finiteCanonicalCameraSynthesis C) X) = X
  rw [finiteHilbertMatrixSynthesis_comp]
  rw [finiteCanonicalCameraReadout_synthesis hG]
  exact finiteHilbertMatrixSynthesis_one X

theorem finiteCanonicalEnrichedCameraHilbert_parseval
    {camera state H : Type*}
    [Fintype camera] [Fintype state]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [DecidableEq camera] [DecidableEq state]
    (C : Matrix camera state ℝ)
    (hG : (finiteCameraRowGram C).PosDef)
    (X Y : FiniteHilbertFamily state H) :
    inner ℂ (finiteCanonicalCameraHilbertReadout C X)
        (finiteCanonicalCameraHilbertReadout C Y) +
      inner ℂ
        (finiteHilbertMatrixSynthesis
          (finiteCanonicalCameraBlindProjection C) X)
        (finiteHilbertMatrixSynthesis
          (finiteCanonicalCameraBlindProjection C) Y) =
      inner ℂ X Y := by
  change inner ℂ
      (finiteHilbertMatrixSynthesis (finiteCanonicalCameraReadout C) X)
      (finiteHilbertMatrixSynthesis (finiteCanonicalCameraReadout C) Y) +
      inner ℂ
        (finiteHilbertMatrixSynthesis
          (finiteCanonicalCameraBlindProjection C) X)
        (finiteHilbertMatrixSynthesis
          (finiteCanonicalCameraBlindProjection C) Y) =
    inner ℂ X Y
  rw [finiteHilbertMatrixSynthesis_inner_gram,
    finiteHilbertMatrixSynthesis_inner_gram]
  have hone := finiteHilbertMatrixSynthesis_inner_gram
    (A := (1 : Matrix state state ℝ)) X Y
  rw [finiteHilbertMatrixSynthesis_one X,
    finiteHilbertMatrixSynthesis_one Y] at hone
  rw [hone]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hP := finiteCanonicalEnrichedCamera_parseval hG
  have hentry := congr_fun (congr_fun hP i) j
  rw [← add_mul]
  congr 1
  have hentry' :
      ((finiteCanonicalCameraReadout C)ᵀ * finiteCanonicalCameraReadout C) i j +
          ((finiteCanonicalCameraBlindProjection C)ᵀ *
            finiteCanonicalCameraBlindProjection C) i j =
        (1 : Matrix state state ℝ) i j := by
    simpa [Matrix.transpose_transpose] using hentry
  have hentry'' :
      ((finiteCanonicalCameraReadout C)ᵀ * finiteCanonicalCameraReadout C) i j +
          ((finiteCanonicalCameraBlindProjection C)ᵀ *
            finiteCanonicalCameraBlindProjection C) i j =
        ((1 : Matrix state state ℝ)ᵀ * (1 : Matrix state state ℝ)) i j := by
    simpa [Matrix.transpose_transpose] using hentry'
  exact_mod_cast hentry''

theorem finiteLiteralCameraHilbertRawSynthesis_inner
    {index H : Type*}
    [Fintype index] [DecidableEq index]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (camera : index → ℕ) (cutoff : ℕ)
    (hcamera : ∀ i, 2 ≤ camera i)
    (X Y : FiniteHilbertFamily index H) :
    inner ℂ
        (finiteCameraHilbertRawSynthesis
          (finiteLiteralCameraMatrix cutoff camera) X)
        (finiteCameraHilbertRawSynthesis
          (finiteLiteralCameraMatrix cutoff camera) Y) =
      ∑ i : index, ∑ j : index,
        (((literalFiniteCameraGram cutoff (camera i) (camera j) : ℝ) : ℂ) *
          inner ℂ (X.ofLp i) (Y.ofLp j)) := by
  rw [finiteCameraHilbertRawSynthesis_inner]
  simp_rw [finiteLiteralCameraMatrix_rowGram_apply_eq_literalFiniteCameraGram
    hcamera cutoff]

def restrictCameraResolvedCarryVertical
    {index : Type*} [Fintype index]
    (camera : index → ℕ) :
    CameraResolvedCarryVertical →ₗ[ℂ]
      FiniteHilbertFamily index CarryVerticalL2 :=
  { toFun := fun X => WithLp.toLp (2 : ENNReal) (fun i => X (camera i))
    map_add' := by
      intro X Y
      ext i
      simp
    map_smul' := by
      intro c X
      ext i
      simp }

@[simp] theorem restrictCameraResolvedCarryVertical_apply
    {index : Type*} [Fintype index]
    (camera : index → ℕ) (X : CameraResolvedCarryVertical) (i : index) :
    (restrictCameraResolvedCarryVertical camera X).ofLp i = X (camera i) := by
  rfl

noncomputable def finiteLiteralWhitenedCameraResolvedLogSlopePrefixState
    {index : Type*} [Fintype index] [DecidableEq index]
    (camera : index → ℕ) (cameraCutoff _tfvdCutoff : ℕ) (_time : ℝ) :
    FiniteHilbertFamily (Fin (finiteFamilyWindow cameraCutoff camera))
      CarryVerticalL2 :=
  finiteCanonicalCameraHilbertSynthesis
    (finiteLiteralCameraMatrix cameraCutoff camera)
      (restrictCameraResolvedCarryVertical camera
      (finiteCameraResolvedLogSlopePrefixState _tfvdCutoff _time))

theorem finiteLiteralWhitenedCameraResolvedLogSlopePrefixState_isometry
    {index : Type*} [Fintype index] [DecidableEq index]
    (camera : index → ℕ) (cameraCutoff _tfvdCutoff : ℕ) (_time : ℝ)
    (hG : (finiteCameraRowGram
      (finiteLiteralCameraMatrix cameraCutoff camera)).PosDef)
    (X Y : FiniteHilbertFamily index CarryVerticalL2) :
    inner ℂ
      (finiteCanonicalCameraHilbertSynthesis
        (finiteLiteralCameraMatrix cameraCutoff camera) X)
      (finiteCanonicalCameraHilbertSynthesis
        (finiteLiteralCameraMatrix cameraCutoff camera) Y) =
      inner ℂ X Y := by
  exact finiteCanonicalCameraHilbertSynthesis_isometry
    (finiteLiteralCameraMatrix cameraCutoff camera) hG X Y

theorem finiteHilbertMatrixSynthesis_map_linearMap_commutes
    {input output H K : Type*}
    [Fintype input] [Fintype output]
    [NormedAddCommGroup H] [Module ℂ H]
    [NormedAddCommGroup K] [Module ℂ K]
    (A : Matrix output input ℝ) (T : H →ₗ[ℂ] K)
    (X : FiniteHilbertFamily input H) :
    finiteHilbertMatrixSynthesis A
        (WithLp.toLp (2 : ENNReal) (fun i => T (X.ofLp i))) =
      WithLp.toLp (2 : ENNReal)
        (fun j => T ((finiteHilbertMatrixSynthesis A X).ofLp j)) := by
  apply PiLp.ext
  intro j
  simp only [finiteHilbertMatrixSynthesis_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]

end
end CarrySelfAdjointOperator
