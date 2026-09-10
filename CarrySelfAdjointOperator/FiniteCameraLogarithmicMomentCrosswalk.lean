import CarrySelfAdjointOperator.SixCameraCenteredLogNaimarkVarianceCrosswalk
import CarrySelfAdjointOperator.C3GammaCameraMomentBound
import NativeCarrySpectralWeyl.Finite.Whitening
import Mathlib.Tactic

open scoped BigOperators ENNReal MeasureTheory RealInnerProductSpace Matrix MatrixOrder
open Set MeasureTheory Filter intervalIntegral

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Infinite
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Camera

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

/-!
# Finite camera logarithmic moment crosswalk

The finite moment API in NativeCarrySpectralWeyl is indexed by an arbitrary
finite family of natural camera labels and a common profile period.  The
Naimark realization is instead indexed by the supported CameraIndex subtype.
This file bridges those presentations through the exact overlap kernel.

The first moment is the quadratic form of the existing logarithmic
multiplication operator.  The second moment is recorded as its form
inner (Y e_i) (Y e_j).  The current pin proves membership of every camera
vector in Dom Y, but does not provide a closure-under-Y theorem for
Dom Y; accordingly this file does not claim an operator-valued Y^2 domain
statement.  The six-camera formulas and the variance crosswalk remain exact.
-/

/-! ## Generic finite Naimark synthesis and its domain -/

/-- Raw finite synthesis of supported camera vectors. -/
def finiteCameraNaimarkSynthesis {ι : Type*} [Fintype ι]
    (camera : ι → CameraIndex) (u : ι → ℝ) : NaimarkSpace :=
  ∑ i : ι, u i • naimarkCameraVector (camera i)

/-- The same finite synthesis, carrying the natural logarithmic domain
membership supplied by every explicit camera vector. -/
def finiteCameraNaimarkDomainSynthesis {ι : Type*} [Fintype ι]
    (camera : ι → CameraIndex) (u : ι → ℝ) :
    logarithmicMultiplication.domain :=
  ⟨finiteCameraNaimarkSynthesis camera u, by
    change finiteCameraNaimarkSynthesis camera u ∈ logarithmicMultiplicationDomain
    rw [finiteCameraNaimarkSynthesis]
    exact Submodule.sum_mem logarithmicMultiplicationDomain
      (fun i hi => Submodule.smul_mem logarithmicMultiplicationDomain _
        (naimarkCameraVector_mem_logarithmicMultiplicationDomain
          (camera i)))⟩

/-- The logarithmic multiplication of the finite domain synthesis, written as
the finite sum of logarithmically multiplied camera vectors. -/
def finiteCameraLogarithmicSynthesis {ι : Type*} [Fintype ι]
    (camera : ι → CameraIndex) (u : ι → ℝ) : NaimarkSpace :=
  ∑ i : ι, u i •
    logarithmicMultiplication (cameraLogDomainVector (camera i))

/-- Every finite camera synthesis belongs to the logarithmic domain. -/
theorem finiteCameraNaimarkSynthesis_mem_logarithmicMultiplicationDomain
    {ι : Type*} [Fintype ι] (camera : ι → CameraIndex) (u : ι → ℝ) :
    finiteCameraNaimarkSynthesis camera u ∈
      logarithmicMultiplication.domain :=
  (finiteCameraNaimarkDomainSynthesis camera u).property

/-- Linearity of the partial multiplication map on a finite camera sum. -/
theorem finiteCameraNaimarkDomainSynthesis_apply
    {ι : Type*} [Fintype ι] (camera : ι → CameraIndex) (u : ι → ℝ) :
    logarithmicMultiplication
        (finiteCameraNaimarkDomainSynthesis camera u) =
      finiteCameraLogarithmicSynthesis camera u := by
  classical
  let domainSum (s : Finset ι) : logarithmicMultiplication.domain :=
    ⟨(∑ i ∈ s, u i • naimarkCameraVector (camera i)), by
      exact Submodule.sum_mem logarithmicMultiplicationDomain
        (fun i hi => Submodule.smul_mem logarithmicMultiplicationDomain _
          (naimarkCameraVector_mem_logarithmicMultiplicationDomain
            (camera i)))⟩
  have hsum (s : Finset ι) :
      logarithmicMultiplication (domainSum s) =
        ∑ i ∈ s, u i • logarithmicMultiplication
          (cameraLogDomainVector (camera i)) := by
    induction s using Finset.induction_on with
    | empty =>
        change logarithmicMultiplication
          (0 : logarithmicMultiplication.domain) = 0
        exact LinearPMap.map_zero logarithmicMultiplication
    | @insert a s ha ih =>
        have hsingle :
            (⟨u a • naimarkCameraVector (camera a),
                Submodule.smul_mem logarithmicMultiplicationDomain _
                  (naimarkCameraVector_mem_logarithmicMultiplicationDomain
                    (camera a))⟩ : logarithmicMultiplication.domain) =
              u a • cameraLogDomainVector (camera a) := by
          apply Subtype.ext
          rfl
        have hadd :
            domainSum (insert a s) =
              (⟨u a • naimarkCameraVector (camera a),
                Submodule.smul_mem logarithmicMultiplicationDomain _
                  (naimarkCameraVector_mem_logarithmicMultiplicationDomain
                    (camera a))⟩ : logarithmicMultiplication.domain) +
              domainSum s := by
          apply Subtype.ext
          change (∑ i ∈ insert a s, u i • naimarkCameraVector (camera i)) =
            u a • naimarkCameraVector (camera a) +
              ∑ i ∈ s, u i • naimarkCameraVector (camera i)
          simp [ha]
        rw [hadd, hsingle, LinearPMap.map_add, LinearPMap.map_smul, ih]
        simp [ha]
  have hdom :
      finiteCameraNaimarkDomainSynthesis camera u =
        domainSum Finset.univ := by
    apply Subtype.ext
    rfl
  rw [hdom]
  exact hsum Finset.univ

/-! ## Column moment identities -/

/-- The existing centered Naimark vector gives the exact decomposition
Y e_c = d_c + log(slope_c) e_c. -/
theorem logarithmicMultiplication_cameraLogDomainVector_eq_centered_add
    (camera : CameraIndex) :
    logarithmicMultiplication (cameraLogDomainVector camera) =
      centeredNaimarkCameraVector camera +
        Real.log (cameraSlope (cameraLabel camera) : ℝ) •
          naimarkCameraVector camera := by
  rw [centeredNaimarkCameraVector]
  change logarithmicMultiplication (cameraLogDomainVector camera) =
    (logarithmicMultiplication (cameraLogDomainVector camera) -
      Real.log (cameraSlope (cameraLabel camera) : ℝ) •
        naimarkCameraVector camera) +
      Real.log (cameraSlope (cameraLabel camera) : ℝ) •
        naimarkCameraVector camera
  simp only [sub_eq_add_neg]
  abel

/-- Mixed raw first moment of two Naimark camera columns. -/
theorem inner_naimarkCameraVector_logarithmicMultiplication
    (b c : CameraIndex) :
    inner ℝ (naimarkCameraVector b)
      (logarithmicMultiplication (cameraLogDomainVector c)) =
      gramKernel b c *
        Real.log (min (cameraSlope (cameraLabel b))
          (cameraSlope (cameraLabel c)) : ℕ) := by
  rw [logarithmicMultiplication_cameraLogDomainVector_eq_centered_add c,
    inner_add_right, real_inner_smul_right,
    inner_naimarkCameraVector_centeredNaimarkCameraVector,
    inner_naimarkCameraVector]
  have hmin : Real.log (min (cameraSlope (cameraLabel b))
      (cameraSlope (cameraLabel c)) : ℕ) -
        Real.log (cameraSlope (cameraLabel c) : ℕ) +
        Real.log (cameraSlope (cameraLabel c) : ℝ) =
      Real.log (min (cameraSlope (cameraLabel b))
        (cameraSlope (cameraLabel c)) : ℕ) := by
    push_cast
    ring
  calc
    gramKernel b c *
        (Real.log (min (cameraSlope (cameraLabel b))
          (cameraSlope (cameraLabel c)) : ℕ) -
          Real.log (cameraSlope (cameraLabel c) : ℕ)) +
      Real.log (cameraSlope (cameraLabel c) : ℝ) *
        gramKernel b c =
      gramKernel b c *
        (Real.log (min (cameraSlope (cameraLabel b))
          (cameraSlope (cameraLabel c)) : ℕ) -
          Real.log (cameraSlope (cameraLabel c) : ℕ) +
          Real.log (cameraSlope (cameraLabel c) : ℝ)) := by
            ring
    _ = gramKernel b c *
        Real.log (min (cameraSlope (cameraLabel b))
          (cameraSlope (cameraLabel c)) : ℕ) := by rw [hmin]

/-- The reverse mixed first moment, obtained by real symmetry. -/
theorem inner_logarithmicMultiplication_naimarkCameraVector
    (b c : CameraIndex) :
    inner ℝ
      (logarithmicMultiplication (cameraLogDomainVector b))
      (naimarkCameraVector c) =
      gramKernel b c *
        Real.log (min (cameraSlope (cameraLabel b))
          (cameraSlope (cameraLabel c)) : ℕ) := by
  rw [real_inner_comm, inner_naimarkCameraVector_logarithmicMultiplication]
  rw [gramKernel_comm]
  congr 2
  rw [min_comm]

/-- Mixed raw second moment of two Naimark camera columns.  This is the
quadratic form of Y on the explicit camera domain. -/
theorem inner_logarithmicMultiplication_cameraLogDomainVector
    (b c : CameraIndex) :
    inner ℝ
      (logarithmicMultiplication (cameraLogDomainVector b))
      (logarithmicMultiplication (cameraLogDomainVector c)) =
      gramKernel b c *
        (1 + Real.log (min (cameraSlope (cameraLabel b))
          (cameraSlope (cameraLabel c)) : ℕ) ^ 2) := by
  rw [logarithmicMultiplication_cameraLogDomainVector_eq_centered_add b,
    logarithmicMultiplication_cameraLogDomainVector_eq_centered_add c]
  simp only [inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right,
    inner_centeredNaimarkCameraVector,
    inner_naimarkCameraVector_centeredNaimarkCameraVector,
    inner_centeredNaimarkCameraVector_naimarkCameraVector,
    inner_naimarkCameraVector]
  rw [gramKernel_comm c b]
  rcases le_total (cameraSlope (cameraLabel b))
      (cameraSlope (cameraLabel c)) with hbc | hcb
  · rw [min_eq_left hbc]
    push_cast
    have hbc' : (cameraSlope (cameraLabel b) : ℝ) ≤
        (cameraSlope (cameraLabel c) : ℝ) := by
      exact_mod_cast hbc
    rw [min_eq_right hbc']
    ring
  · rw [min_eq_right hcb]
    push_cast
    have hcb' : (cameraSlope (cameraLabel c) : ℝ) ≤
        (cameraSlope (cameraLabel b) : ℝ) := by
      exact_mod_cast hcb
    rw [min_eq_left hcb']
    ring

/-! ## Kernel moment matrices -/

/-- Gram matrix of a finite family of explicit Naimark columns. -/
def finiteCameraNaimarkGramMatrix {ι : Type*}
    (camera : ι → CameraIndex) : Matrix ι ι ℝ :=
  fun i j => gramKernel (camera i) (camera j)

/-- First logarithmic moment matrix of the same columns. -/
def finiteCameraNaimarkFirstMomentMatrix {ι : Type*}
    (camera : ι → CameraIndex) : Matrix ι ι ℝ :=
  fun i j => gramKernel (camera i) (camera j) *
    Real.log (min (cameraSlope (cameraLabel (camera i)))
      (cameraSlope (cameraLabel (camera j))) : ℕ)

/-- Second logarithmic moment matrix in form sense. -/
def finiteCameraNaimarkSecondMomentMatrix {ι : Type*}
    (camera : ι → CameraIndex) : Matrix ι ι ℝ :=
  fun i j => gramKernel (camera i) (camera j) *
    (1 + Real.log (min (cameraSlope (cameraLabel (camera i)))
      (cameraSlope (cameraLabel (camera j))) : ℕ) ^ 2)

/-- Raw synthesis Gram identity. -/
theorem finiteCameraNaimarkSynthesis_inner
    {ι : Type*} [Fintype ι] (camera : ι → CameraIndex)
    (u v : ι → ℝ) :
    inner ℝ (finiteCameraNaimarkSynthesis camera u)
      (finiteCameraNaimarkSynthesis camera v) =
      u ⬝ᵥ (finiteCameraNaimarkGramMatrix camera *ᵥ v) := by
  classical
  simp only [finiteCameraNaimarkSynthesis, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right,
    inner_naimarkCameraVector]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [finiteCameraNaimarkGramMatrix]
  ring

/-- Raw first moment identity. -/
theorem finiteCameraNaimarkSynthesis_log_inner
    {ι : Type*} [Fintype ι] (camera : ι → CameraIndex)
    (u v : ι → ℝ) :
    inner ℝ (finiteCameraNaimarkSynthesis camera u)
      (finiteCameraLogarithmicSynthesis camera v) =
      u ⬝ᵥ (finiteCameraNaimarkFirstMomentMatrix camera *ᵥ v) := by
  classical
  simp only [finiteCameraNaimarkSynthesis, finiteCameraLogarithmicSynthesis,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [inner_naimarkCameraVector_logarithmicMultiplication]
  rw [finiteCameraNaimarkFirstMomentMatrix]
  ring

/-- Raw second-moment form identity. -/
theorem finiteCameraLogarithmicSynthesis_inner
    {ι : Type*} [Fintype ι] (camera : ι → CameraIndex)
    (u v : ι → ℝ) :
    inner ℝ (finiteCameraLogarithmicSynthesis camera u)
      (finiteCameraLogarithmicSynthesis camera v) =
      u ⬝ᵥ (finiteCameraNaimarkSecondMomentMatrix camera *ᵥ v) := by
  classical
  simp only [finiteCameraLogarithmicSynthesis, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [inner_logarithmicMultiplication_cameraLogDomainVector]
  rw [finiteCameraNaimarkSecondMomentMatrix]
  ring

/-! ## Comparison with the period-indexed upstream matrices -/

/-- Pairwise periodic Gram agreement is the only hypothesis needed for the
generic finite-moment source matrices. -/
theorem finiteCameraNaimarkGramMatrix_eq_periodicGramMatrix
    {ι : Type*} [Fintype ι] (period : ℕ)
    (camera : ι → CameraIndex)
    (hgram : ∀ i j,
      periodicGramMatrix period
          (fun i => cameraLabel (camera i)) i j =
        gramKernel (camera i) (camera j)) :
    finiteCameraNaimarkGramMatrix camera =
      periodicGramMatrix period
        (fun i => cameraLabel (camera i)) := by
  ext i j
  rw [finiteCameraNaimarkGramMatrix, hgram]

/-- Pairwise periodic first-moment agreement. -/
theorem finiteCameraNaimarkFirstMomentMatrix_eq_firstMomentMatrix
    {ι : Type*} [Fintype ι] (period : ℕ)
    (camera : ι → CameraIndex)
    (hgram : ∀ i j,
      periodicGramMatrix period
          (fun i => cameraLabel (camera i)) i j =
        gramKernel (camera i) (camera j)) :
    finiteCameraNaimarkFirstMomentMatrix camera =
      firstMomentMatrix period
        (fun i => cameraLabel (camera i)) := by
  ext i j
  rw [finiteCameraNaimarkFirstMomentMatrix, firstMomentMatrix_apply, hgram]
  rfl

/-- Pairwise periodic second-moment agreement. -/
theorem finiteCameraNaimarkSecondMomentMatrix_eq_secondCenteredMomentMatrix
    {ι : Type*} [Fintype ι] (period : ℕ)
    (camera : ι → CameraIndex)
    (hgram : ∀ i j,
      periodicGramMatrix period
          (fun i => cameraLabel (camera i)) i j =
        gramKernel (camera i) (camera j)) :
    finiteCameraNaimarkSecondMomentMatrix camera =
      secondCenteredMomentMatrix period
        (fun i => cameraLabel (camera i)) := by
  ext i j
  rw [finiteCameraNaimarkSecondMomentMatrix,
    secondCenteredMomentMatrix_apply, hgram]
  rfl

/-- The exact period-420 Gram agreement for the six-camera indexing. -/
theorem atlasSixCamera_periodicGram_eq_gramKernel (i j : Fin 6) :
    periodicGramMatrix 420 sixCamera i j =
      gramKernel (atlasSixCameraIndex i) (atlasSixCameraIndex j) := by
  rw [sixCameraGram_eq, atlasSixCameraGram_entry_eq_gramKernel]

/-- The labels carried by the supported six-camera subtype are the literal
labels 2, ..., 7. -/
theorem atlasSixCamera_labels_eq_sixCamera :
    (fun i : Fin 6 => cameraLabel (atlasSixCameraIndex i)) = sixCamera := by
  funext i
  rfl

theorem finiteCameraNaimarkGramMatrix_six_eq :
    finiteCameraNaimarkGramMatrix atlasSixCameraIndex = sixCameraGram := by
  have hgram : ∀ i j : Fin 6,
      periodicGramMatrix 420
          (fun i : Fin 6 => cameraLabel (atlasSixCameraIndex i)) i j =
        gramKernel (atlasSixCameraIndex i) (atlasSixCameraIndex j) := by
    intro i j
    rw [atlasSixCamera_labels_eq_sixCamera]
    exact atlasSixCamera_periodicGram_eq_gramKernel i j
  rw [finiteCameraNaimarkGramMatrix_eq_periodicGramMatrix
    420 atlasSixCameraIndex hgram, atlasSixCamera_labels_eq_sixCamera,
    sixCameraGram_eq]

theorem finiteCameraNaimarkFirstMomentMatrix_six_eq :
    finiteCameraNaimarkFirstMomentMatrix atlasSixCameraIndex =
      sixCameraFirstMoment := by
  have hgram : ∀ i j : Fin 6,
      periodicGramMatrix 420
          (fun i : Fin 6 => cameraLabel (atlasSixCameraIndex i)) i j =
        gramKernel (atlasSixCameraIndex i) (atlasSixCameraIndex j) := by
    intro i j
    rw [atlasSixCamera_labels_eq_sixCamera]
    exact atlasSixCamera_periodicGram_eq_gramKernel i j
  rw [finiteCameraNaimarkFirstMomentMatrix_eq_firstMomentMatrix
    420 atlasSixCameraIndex hgram, atlasSixCamera_labels_eq_sixCamera]
  exact sixCameraFirstMoment_eq

theorem finiteCameraNaimarkSecondMomentMatrix_six_eq :
    finiteCameraNaimarkSecondMomentMatrix atlasSixCameraIndex =
      sixCameraSecondCenteredMoment := by
  have hgram : ∀ i j : Fin 6,
      periodicGramMatrix 420
          (fun i : Fin 6 => cameraLabel (atlasSixCameraIndex i)) i j =
        gramKernel (atlasSixCameraIndex i) (atlasSixCameraIndex j) := by
    intro i j
    rw [atlasSixCamera_labels_eq_sixCamera]
    exact atlasSixCamera_periodicGram_eq_gramKernel i j
  rw [finiteCameraNaimarkSecondMomentMatrix_eq_secondCenteredMomentMatrix
    420 atlasSixCameraIndex hgram, atlasSixCamera_labels_eq_sixCamera]
  exact sixCameraSecondCenteredMoment_eq

/-! ## Whitened synthesis and moment compressions -/

/-- Whitened raw finite Naimark synthesis. -/
def finiteCameraWhitenedNaimarkSynthesis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ) (u : ι → ℝ) :
    NaimarkSpace :=
  finiteCameraNaimarkSynthesis camera (positiveInverseSqrt G *ᵥ u)

/-- Whitened logarithmic finite synthesis. -/
def finiteCameraWhitenedLogarithmicSynthesis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ) (u : ι → ℝ) :
    NaimarkSpace :=
  finiteCameraLogarithmicSynthesis camera (positiveInverseSqrt G *ᵥ u)

/-- Whitened raw synthesis pairing before imposing that the supplied matrix is
its actual raw Gram. -/
theorem finiteCameraWhitenedNaimarkSynthesis_inner_matrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (u v : ι → ℝ) :
    inner ℝ (finiteCameraWhitenedNaimarkSynthesis camera G u)
      (finiteCameraWhitenedNaimarkSynthesis camera G v) =
      u ⬝ᵥ (((positiveInverseSqrt G)ᵀ *
        finiteCameraNaimarkGramMatrix camera *
        positiveInverseSqrt G) *ᵥ v) := by
  rw [finiteCameraWhitenedNaimarkSynthesis,
    finiteCameraWhitenedNaimarkSynthesis,
    finiteCameraNaimarkSynthesis_inner]
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- If the supplied matrix is the raw Gram of the camera family, its
positive-definite whitening makes the finite Naimark synthesis an isometry. -/
theorem finiteCameraWhitenedNaimarkSynthesis_inner
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (hGram : finiteCameraNaimarkGramMatrix camera = G)
    (hG : G.PosDef) (u v : ι → ℝ) :
    inner ℝ (finiteCameraWhitenedNaimarkSynthesis camera G u)
      (finiteCameraWhitenedNaimarkSynthesis camera G v) =
      u ⬝ᵥ v := by
  rw [finiteCameraWhitenedNaimarkSynthesis_inner_matrix, hGram]
  have hR := positiveInverseSqrt_isHermitian hG
  have hRT : (positiveInverseSqrt G)ᵀ =
      positiveInverseSqrt G := by
    ext i j
    simpa only [Matrix.transpose_apply, Matrix.conjTranspose_apply,
      star_trivial] using congr_fun (congr_fun hR.eq i) j
  rw [hRT, positiveInverseSqrt_whitens hG]
  simp

/-- Whitened first-moment compression in form notation. -/
theorem finiteCameraWhitenedNaimarkSynthesis_log_inner
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (u v : ι → ℝ) :
    inner ℝ (finiteCameraWhitenedNaimarkSynthesis camera G u)
      (finiteCameraWhitenedLogarithmicSynthesis camera G v) =
      u ⬝ᵥ (((positiveInverseSqrt G)ᵀ *
        finiteCameraNaimarkFirstMomentMatrix camera *
        positiveInverseSqrt G) *ᵥ v) := by
  rw [finiteCameraWhitenedNaimarkSynthesis,
    finiteCameraWhitenedLogarithmicSynthesis,
    finiteCameraNaimarkSynthesis_log_inner]
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- Whitened second-moment compression in form notation. -/
theorem finiteCameraWhitenedLogarithmicSynthesis_inner
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (u v : ι → ℝ) :
    inner ℝ (finiteCameraWhitenedLogarithmicSynthesis camera G u)
      (finiteCameraWhitenedLogarithmicSynthesis camera G v) =
      u ⬝ᵥ (((positiveInverseSqrt G)ᵀ *
        finiteCameraNaimarkSecondMomentMatrix camera *
        positiveInverseSqrt G) *ᵥ v) := by
  rw [finiteCameraWhitenedLogarithmicSynthesis,
    finiteCameraWhitenedLogarithmicSynthesis,
    finiteCameraLogarithmicSynthesis_inner]
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- Domain membership for every whitened finite synthesis. -/
theorem finiteCameraWhitenedNaimarkSynthesis_mem_domain
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ) (u : ι → ℝ) :
    finiteCameraWhitenedNaimarkSynthesis camera G u ∈
      logarithmicMultiplication.domain :=
  finiteCameraNaimarkSynthesis_mem_logarithmicMultiplicationDomain
    camera (positiveInverseSqrt G *ᵥ u)

/-- A whitened finite logarithmic synthesis is the image under the natural
partial logarithmic multiplier of the corresponding domain element. -/
theorem finiteCameraWhitenedLogarithmicSynthesis_eq_logarithmicMultiplication
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ) (u : ι → ℝ) :
    finiteCameraWhitenedLogarithmicSynthesis camera G u =
      logarithmicMultiplication
        (finiteCameraNaimarkDomainSynthesis camera
          (positiveInverseSqrt G *ᵥ u)) := by
  symm
  exact finiteCameraNaimarkDomainSynthesis_apply camera
    (positiveInverseSqrt G *ᵥ u)

/-- Generic first compression written with the existing whitening matrix. -/
theorem finiteCameraWhitenedLogarithmicCompression
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ) :
    (fun i j => inner ℝ
      (finiteCameraWhitenedNaimarkSynthesis camera G
        (Pi.single i 1))
      (finiteCameraWhitenedLogarithmicSynthesis camera G
        (Pi.single j 1))) =
      (fun i j => ((positiveInverseSqrt G)ᵀ *
        finiteCameraNaimarkFirstMomentMatrix camera *
        positiveInverseSqrt G) i j) := by
  funext i j
  simpa [dotProduct, Pi.single_apply] using
    finiteCameraWhitenedNaimarkSynthesis_log_inner camera G
      (Pi.single i 1) (Pi.single j 1)

/-- Generic second compression written with the existing whitening matrix. -/
theorem finiteCameraWhitenedSecondMomentCompression
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ) :
    (fun i j => inner ℝ
      (finiteCameraWhitenedLogarithmicSynthesis camera G
        (Pi.single i 1))
      (finiteCameraWhitenedLogarithmicSynthesis camera G
        (Pi.single j 1))) =
      (fun i j => ((positiveInverseSqrt G)ᵀ *
        finiteCameraNaimarkSecondMomentMatrix camera *
        positiveInverseSqrt G) i j) := by
  funext i j
  simpa [dotProduct, Pi.single_apply] using
    finiteCameraWhitenedLogarithmicSynthesis_inner camera G
      (Pi.single i 1) (Pi.single j 1)

/-! ## Six-camera aliases and exact moment crosswalks -/

/-- Six-camera raw logarithmic synthesis, using the existing finite package. -/
def sixCameraLogarithmicSynthesis (u : Fin 6 → ℝ) : NaimarkSpace :=
  finiteCameraLogarithmicSynthesis atlasSixCameraIndex u

/-- Six-camera whitened logarithmic synthesis. -/
def sixCameraWhitenedLogarithmicSynthesis (u : Fin 6 → ℝ) :
    NaimarkSpace :=
  finiteCameraWhitenedLogarithmicSynthesis atlasSixCameraIndex
    sixCameraGram u

theorem finiteCameraNaimarkSynthesis_six_eq
    (u : Fin 6 → ℝ) :
    finiteCameraNaimarkSynthesis atlasSixCameraIndex u =
      sixCameraNaimarkSynthesis u := by
  rfl

theorem finiteCameraLogarithmicSynthesis_six_eq
    (u : Fin 6 → ℝ) :
    finiteCameraLogarithmicSynthesis atlasSixCameraIndex u =
      sixCameraLogarithmicSynthesis u := by
  rfl

theorem sixCameraWhitenedNaimarkSynthesis_mem_domain
    (u : Fin 6 → ℝ) :
    sixCameraWhitenedNaimarkSynthesis u ∈
      logarithmicMultiplication.domain := by
  exact finiteCameraWhitenedNaimarkSynthesis_mem_domain
    atlasSixCameraIndex sixCameraGram u

theorem sixCameraWhitenedLogarithmicSynthesis_eq_logarithmicMultiplication
    (u : Fin 6 → ℝ) :
    sixCameraWhitenedLogarithmicSynthesis u =
      logarithmicMultiplication
        (finiteCameraNaimarkDomainSynthesis atlasSixCameraIndex
          (positiveInverseSqrt sixCameraGram *ᵥ u)) := by
  exact finiteCameraWhitenedLogarithmicSynthesis_eq_logarithmicMultiplication
    atlasSixCameraIndex sixCameraGram u

theorem sixCameraWhitenedNaimarkSynthesis_log_inner
    (u v : Fin 6 → ℝ) :
    inner ℝ (sixCameraWhitenedNaimarkSynthesis u)
      (sixCameraWhitenedLogarithmicSynthesis v) =
      u ⬝ᵥ (sixCameraLogOperator *ᵥ v) := by
  change inner ℝ
      (finiteCameraWhitenedNaimarkSynthesis atlasSixCameraIndex
        sixCameraGram u)
      (finiteCameraWhitenedLogarithmicSynthesis atlasSixCameraIndex
        sixCameraGram v) =
    u ⬝ᵥ (sixCameraLogOperator *ᵥ v)
  rw [finiteCameraWhitenedNaimarkSynthesis_log_inner
      atlasSixCameraIndex sixCameraGram]
  rw [finiteCameraNaimarkFirstMomentMatrix_six_eq]
  have hR := positiveInverseSqrt_isHermitian sixCameraGram_posDef
  have hRT : (positiveInverseSqrt sixCameraGram)ᵀ =
      positiveInverseSqrt sixCameraGram := by
    ext i j
    simpa only [Matrix.transpose_apply, Matrix.conjTranspose_apply,
      star_trivial] using congr_fun (congr_fun hR.eq i) j
  rw [hRT]
  rfl

theorem sixCameraWhitenedLogarithmicSynthesis_inner
    (u v : Fin 6 → ℝ) :
    inner ℝ (sixCameraWhitenedLogarithmicSynthesis u)
      (sixCameraWhitenedLogarithmicSynthesis v) =
      u ⬝ᵥ (sixCameraWhitenedSecondMoment *ᵥ v) := by
  change inner ℝ
      (finiteCameraWhitenedLogarithmicSynthesis atlasSixCameraIndex
        sixCameraGram u)
      (finiteCameraWhitenedLogarithmicSynthesis atlasSixCameraIndex
        sixCameraGram v) =
    u ⬝ᵥ (sixCameraWhitenedSecondMoment *ᵥ v)
  rw [finiteCameraWhitenedLogarithmicSynthesis_inner
      atlasSixCameraIndex sixCameraGram,
    finiteCameraNaimarkSecondMomentMatrix_six_eq]
  have hR := positiveInverseSqrt_isHermitian sixCameraGram_posDef
  have hRT : (positiveInverseSqrt sixCameraGram)ᵀ =
      positiveInverseSqrt sixCameraGram := by
    ext i j
    simpa only [Matrix.transpose_apply, Matrix.conjTranspose_apply,
      star_trivial] using congr_fun (congr_fun hR.eq i) j
  rw [hRT]
  rfl

theorem sixCameraWhitenedNaimarkSynthesis_inner_eq_identity
    (u v : Fin 6 → ℝ) :
    inner ℝ (sixCameraWhitenedNaimarkSynthesis u)
      (sixCameraWhitenedNaimarkSynthesis v) =
      u ⬝ᵥ v :=
  sixCameraWhitenedNaimarkSynthesis_inner u v

/-! ## Compression defect and the existing centered-log crosswalk -/

/-- The generic whitening defect is the usual finite variance operator. -/
def finiteCameraLogarithmicVariance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G H J : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  varianceOperator G H J

theorem finiteCameraLogarithmicVariance_eq_compression_defect
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G H J : Matrix ι ι ℝ) :
    finiteCameraLogarithmicVariance G H J =
      whitenedSecondMoment G J -
        whitenedFirstMoment G H * whitenedFirstMoment G H := by
  rfl

theorem sixCameraVariance_eq_logarithmic_compression_defect :
    sixCameraVariance =
      sixCameraWhitenedSecondMoment - sixCameraLogOperator *
        sixCameraLogOperator := by
  rfl

theorem sixCameraVariance_eq_centered_logarithmic_form :
    (fun u v : Fin 6 → ℝ =>
      inner ℝ (sixCameraWhitenedCenteredLogNaimarkSynthesis u -
        sixCameraWhitenedNaimarkSynthesis
          (sixCameraWhitenedCrossGram *ᵥ u))
        (sixCameraWhitenedCenteredLogNaimarkSynthesis v -
        sixCameraWhitenedNaimarkSynthesis
          (sixCameraWhitenedCrossGram *ᵥ v))) =
      (fun u v => u ⬝ᵥ (sixCameraVariance *ᵥ v)) := by
  funext u v
  rw [← sixCameraWhitenedNaimarkEscape_centeredLog u,
    ← sixCameraWhitenedNaimarkEscape_centeredLog v]
  exact sixCameraWhitenedNaimarkEscape_centeredLog_inner u v

/-- The raw moment form and the already-proved centered Naimark escape form
are two exact presentations of the same six-camera variance. -/
theorem sixCameraLogarithmicCompressionDefect_eq_centeredNaimarkEscape :
    (fun u v : Fin 6 → ℝ =>
      u ⬝ᵥ ((sixCameraWhitenedSecondMoment -
        sixCameraLogOperator * sixCameraLogOperator) *ᵥ v)) =
      (fun u v : Fin 6 → ℝ =>
        inner ℝ
          (sixCameraWhitenedNaimarkEscape
            (sixCameraWhitenedCenteredLogNaimarkSynthesis u))
          (sixCameraWhitenedNaimarkEscape
            (sixCameraWhitenedCenteredLogNaimarkSynthesis v))) := by
  funext u v
  have hvar : sixCameraWhitenedSecondMoment -
      sixCameraLogOperator * sixCameraLogOperator =
      sixCameraVariance := by
    symm
    exact sixCameraVariance_eq_logarithmic_compression_defect
  rw [hvar]
  exact (sixCameraWhitenedNaimarkEscape_centeredLog_inner u v).symm

end
end CarrySelfAdjointOperator
