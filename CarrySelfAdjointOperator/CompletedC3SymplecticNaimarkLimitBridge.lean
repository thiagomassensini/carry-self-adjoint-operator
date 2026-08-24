import CarrySelfAdjointOperator.CanonicalC3SymplecticNaimarkBridge
import CarrySelfAdjointOperator.CompletedC3FNegFPrimeMixedKernel
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Tactic

/-!
# All-cutoff symplectic C3--Naimark bridge

The fixed three-cell symplectic bridge proves the correct order
`rotation -> real readout`.  This file makes the construction uniform in the
finite cutoff.  Every complex cell uses the two permanent real coordinates
`2 n` and `2 n + 1` in one infinite orthonormal camera family.  Consequently
all finite C3 ports land in the same global camera and Naimark spaces.

Two real skew readings retain the two quadratures separately.  The first
reads `re (greenForm x y)`; the second reads
`re (greenForm x (i y)) = -im (greenForm x y)`.  Complex reconstruction is
performed only after both readings, and recovers the full polarized complex
Green form exactly.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite
open Filter

open scoped ComplexConjugate RealInnerProductSpace

noncomputable section

/-! ## One permanent orthonormal camera family -/

/-- Camera label `n + 2` reserved for the `n`-th real completion
coordinate. -/
def completedC3RealCameraIndex (n : ℕ) : CameraIndex :=
  ⟨n + 2, by omega⟩

theorem completedC3RealCameraIndex_injective :
    Function.Injective completedC3RealCameraIndex := by
  intro m n hmn
  have hval := congrArg Subtype.val hmn
  simp [completedC3RealCameraIndex] at hval
  omega

/-- Infinite independent family of literal camera vectors. -/
def completedC3RawCameraVector (n : ℕ) : CameraHilbert :=
  cameraVector (completedC3RealCameraIndex n)

theorem completedC3RawCameraVector_linearIndependent :
    LinearIndependent ℝ completedC3RawCameraVector := by
  have hsingle : LinearIndependent ℝ
      (fun camera : CameraIndex ↦
        Finsupp.single camera (1 : ℝ) : CameraIndex → CameraFinsupp) :=
    Finsupp.linearIndependent_single_one ℝ CameraIndex
  have hrestricted : LinearIndependent ℝ
      (fun n : ℕ ↦
        Finsupp.single (completedC3RealCameraIndex n) (1 : ℝ)) :=
    hsingle.comp completedC3RealCameraIndex
      completedC3RealCameraIndex_injective
  exact hrestricted.map' cameraEmbedding.toLinearMap
    (LinearMap.ker_eq_bot.mpr cameraEmbedding.injective)

/-- One orthonormal camera family shared by every cutoff. -/
def completedC3OrthonormalCameraVector (n : ℕ) : CameraHilbert :=
  InnerProductSpace.gramSchmidtNormed ℝ completedC3RawCameraVector n

theorem completedC3OrthonormalCameraVector_orthonormal :
    Orthonormal ℝ completedC3OrthonormalCameraVector :=
  InnerProductSpace.gramSchmidtNormed_orthonormal
    completedC3RawCameraVector_linearIndependent

/-! ## Explicit real/imaginary coordinates at an arbitrary cutoff -/

/-- Two real quadratures for each of the `M` complex C3 cells. -/
abbrev FiniteC3RealCoordinate (M : ℕ) := Fin M × Fin 2

/-- Permanent global coordinate of one finite real/imaginary cell. -/
def finiteC3RealCoordinateNat {M : ℕ}
    (j : FiniteC3RealCoordinate M) : ℕ :=
  2 * j.1.val + j.2.val

theorem finiteC3RealCoordinateNat_injective (M : ℕ) :
    Function.Injective (@finiteC3RealCoordinateNat M) := by
  intro i j hij
  apply Prod.ext
  · apply Fin.ext
    dsimp [finiteC3RealCoordinateNat] at hij
    omega
  · apply Fin.ext
    dsimp [finiteC3RealCoordinateNat] at hij
    omega

/-- Explicit real/imaginary coordinate map for a finite complex C3 leg. -/
def finiteC3LegRealCoordinateLinearMap (M : ℕ) :
    NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace M →ₗ[ℝ]
      EuclideanSpace ℝ (FiniteC3RealCoordinate M) where
  toFun x := WithLp.toLp 2
    (fun j ↦ ![(x j.1).re, (x j.1).im] j.2)
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    funext j
    rcases j with ⟨j, k⟩
    fin_cases k <;> simp
  map_smul' r x := by
    apply WithLp.ofLp_injective 2
    funext j
    rcases j with ⟨j, k⟩
    fin_cases k <;> simp

@[simp] theorem finiteC3LegRealCoordinateLinearMap_apply
    (M : ℕ)
    (x : NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace M)
    (j : FiniteC3RealCoordinate M) :
    finiteC3LegRealCoordinateLinearMap M x j =
      ![(x j.1).re, (x j.1).im] j.2 :=
  rfl

/-- Explicit coordinates preserve the coordinatewise real inner product. -/
theorem finiteC3LegRealCoordinateLinearMap_inner
    (M : ℕ)
    (x y : NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace M) :
    inner ℝ (finiteC3LegRealCoordinateLinearMap M x)
        (finiteC3LegRealCoordinateLinearMap M y) =
      inner ℝ x y := by
  simp [PiLp.inner_apply, finiteC3LegRealCoordinateLinearMap,
    Fintype.sum_prod_type, Fin.sum_univ_two,
    real_inner_eq_re_inner ℂ]

/-- Isometric explicit realification of a finite C3 leg. -/
def finiteC3LegRealCoordinateIsometry (M : ℕ) :
    NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace M →ₗᵢ[ℝ]
      EuclideanSpace ℝ (FiniteC3RealCoordinate M) :=
  (finiteC3LegRealCoordinateLinearMap M).isometryOfInner
    (finiteC3LegRealCoordinateLinearMap_inner M)

/-! ## Uniform finite-coordinate synthesis in the camera completion -/

/-- Synthesis of one finite coordinate block through the permanent camera
family. -/
def finiteC3CameraCoordinateLinearMap (M : ℕ) :
    EuclideanSpace ℝ (FiniteC3RealCoordinate M) →ₗ[ℝ] CameraHilbert where
  toFun x := ∑ j : FiniteC3RealCoordinate M,
    x j • completedC3OrthonormalCameraVector
      (finiteC3RealCoordinateNat j)
  map_add' x y := by
    simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [PiLp.smul_apply, RingHom.id_apply, smul_eq_mul,
      smul_smul, Finset.smul_sum]

@[simp] theorem finiteC3CameraCoordinateLinearMap_basisFun
    (M : ℕ) (j : FiniteC3RealCoordinate M) :
    finiteC3CameraCoordinateLinearMap M
        (EuclideanSpace.basisFun (FiniteC3RealCoordinate M) ℝ j) =
      completedC3OrthonormalCameraVector
        (finiteC3RealCoordinateNat j) := by
  classical
  simp [finiteC3CameraCoordinateLinearMap]

/-- Every finite coordinate block embeds isometrically through the same
infinite camera family. -/
def finiteC3CameraCoordinateIsometry (M : ℕ) :
    EuclideanSpace ℝ (FiniteC3RealCoordinate M) →ₗᵢ[ℝ] CameraHilbert :=
  (finiteC3CameraCoordinateLinearMap M).isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun
      (FiniteC3RealCoordinate M) ℝ).toBasis)
    (EuclideanSpace.basisFun
      (FiniteC3RealCoordinate M) ℝ).orthonormal
    (by
      change Orthonormal ℝ
        (fun j : FiniteC3RealCoordinate M ↦
          finiteC3CameraCoordinateLinearMap M
            (EuclideanSpace.basisFun
              (FiniteC3RealCoordinate M) ℝ j))
      rw [show
        (fun j : FiniteC3RealCoordinate M ↦
          finiteC3CameraCoordinateLinearMap M
            (EuclideanSpace.basisFun
              (FiniteC3RealCoordinate M) ℝ j)) =
          (fun j ↦ completedC3OrthonormalCameraVector
            (finiteC3RealCoordinateNat j)) by
        funext j
        exact finiteC3CameraCoordinateLinearMap_basisFun M j]
      simpa [Function.comp_def] using
        completedC3OrthonormalCameraVector_orthonormal.comp
          finiteC3RealCoordinateNat
          (finiteC3RealCoordinateNat_injective M))

/-- Uniform isometric realization of one finite complex C3 leg in the global
camera Hilbert space. -/
def finiteC3LegCameraIsometry (M : ℕ) :
    NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace M →ₗᵢ[ℝ]
      CameraHilbert :=
  (finiteC3CameraCoordinateIsometry M).comp
    (finiteC3LegRealCoordinateIsometry M)

/-- The real Hilbert structure on every finite complex C3 leg is the real
part of its complex Hilbert structure. -/
theorem finiteC3GreenBoundarySpace_real_inner_eq_re_inner_allCutoff
    (M : ℕ)
    (x y : NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace M) :
    inner ℝ x y = (inner ℂ x y).re := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  calc
    (∑ i, inner ℝ (x i) (y i)) =
        ∑ i, (inner ℂ (x i) (y i)).re := by
      apply Finset.sum_congr rfl
      intro i _
      exact real_inner_eq_re_inner ℂ (x i) (y i)
    _ = (∑ i, inner ℂ (x i) (y i)).re := by
      exact (map_sum Complex.reAddGroupHom
        (fun i ↦ inner ℂ (x i) (y i)) Finset.univ).symm

/-! ## Symplectic port packing and Naimark promotion -/

/-- Corrected symplectic packing at an arbitrary finite cutoff. -/
def finiteC3SymplecticCameraPackingLinearMap (M : ℕ) :
    NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier M →ₗ[ℝ]
      RealifiedCameraComplexification where
  toFun x := WithLp.toLp 2
    (-finiteC3LegCameraIsometry M x.1,
      finiteC3LegCameraIsometry M x.2)
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change
        -finiteC3LegCameraIsometry M (x.1 + y.1) =
          -finiteC3LegCameraIsometry M x.1 +
            -finiteC3LegCameraIsometry M y.1
      rw [map_add]
      abel
    · change
        finiteC3LegCameraIsometry M (x.2 + y.2) =
          finiteC3LegCameraIsometry M x.2 +
            finiteC3LegCameraIsometry M y.2
      rw [map_add]
  map_smul' r x := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change
        -finiteC3LegCameraIsometry M (r • x.1) =
          r • (-finiteC3LegCameraIsometry M x.1)
      rw [map_smul, smul_neg]
    · change
        finiteC3LegCameraIsometry M (r • x.2) =
          r • finiteC3LegCameraIsometry M x.2
      rw [map_smul]

/-- Continuous all-cutoff symplectic packing. -/
def finiteC3SymplecticCameraPacking (M : ℕ) :
    NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier M →L[ℝ]
      RealifiedCameraComplexification :=
  LinearMap.toContinuousLinearMap
    (finiteC3SymplecticCameraPackingLinearMap M)

@[simp] theorem finiteC3SymplecticCameraPacking_apply
    (M : ℕ) (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier M) :
    finiteC3SymplecticCameraPacking M x = WithLp.toLp 2
      (-finiteC3LegCameraIsometry M x.1,
        finiteC3LegCameraIsometry M x.2) :=
  rfl

/-- The all-cutoff packing preserves the real part of the intrinsic Green
form exactly. -/
theorem realifiedGreenSkew_finiteC3SymplecticCameraPacking
    (M : ℕ)
    (x y : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier M) :
    NativeCarryC3Crosswalk.realifiedGreenSkew
        (finiteC3SymplecticCameraPacking M x)
        (finiteC3SymplecticCameraPacking M y) =
      (greenForm (𝕜 := ℂ) x y).re := by
  change
    inner ℝ (-finiteC3LegCameraIsometry M x.1)
        (finiteC3LegCameraIsometry M y.2) -
      inner ℝ (finiteC3LegCameraIsometry M x.2)
        (-finiteC3LegCameraIsometry M y.1) = _
  simp only [inner_neg_left, inner_neg_right]
  rw [(finiteC3LegCameraIsometry M).inner_map_map,
    (finiteC3LegCameraIsometry M).inner_map_map]
  rw [finiteC3GreenBoundarySpace_real_inner_eq_re_inner_allCutoff,
    finiteC3GreenBoundarySpace_real_inner_eq_re_inner_allCutoff]
  simp [greenForm]
  ring

/-- Coordinatewise Naimark realization of the arbitrary-cutoff packing. -/
def finiteC3SymplecticNaimarkRealization (M : ℕ) :
    NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier M →L[ℝ]
      RealifiedNaimarkComplexification :=
  realifiedNaimarkPort ∘L finiteC3SymplecticCameraPacking M

/-- Naimark promotion preserves the arbitrary-cutoff Green skew. -/
theorem realifiedGreenSkew_finiteC3SymplecticNaimarkRealization
    (M : ℕ)
    (x y : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier M) :
    NativeCarryC3Crosswalk.realifiedGreenSkew
        (finiteC3SymplecticNaimarkRealization M x)
        (finiteC3SymplecticNaimarkRealization M y) =
      (greenForm (𝕜 := ℂ) x y).re := by
  rw [show finiteC3SymplecticNaimarkRealization M x =
      realifiedNaimarkPort (finiteC3SymplecticCameraPacking M x) from rfl,
    show finiteC3SymplecticNaimarkRealization M y =
      realifiedNaimarkPort (finiteC3SymplecticCameraPacking M y) from rfl,
    NativeCarryC3Crosswalk.realifiedGreenSkew_realifiedNaimarkPort]
  exact realifiedGreenSkew_finiteC3SymplecticCameraPacking M x y

/-! ## Lossless two-quadrature complex readout -/

/-- The two real Naimark skew readings are retained as separate channels.
The quarter-turn channel is evaluated before any real-part projection. -/
structure FiniteC3SymplecticGreenQuadratures where
  direct : ℝ
  quarterTurn : ℝ

/-- Direct and quarter-turned skew readings of a finite complex Green pair. -/
def finiteC3SymplecticNaimarkGreenQuadratures
    (M : ℕ)
    (x y : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier M) :
    FiniteC3SymplecticGreenQuadratures where
  direct := NativeCarryC3Crosswalk.realifiedGreenSkew
    (finiteC3SymplecticNaimarkRealization M x)
    (finiteC3SymplecticNaimarkRealization M y)
  quarterTurn := NativeCarryC3Crosswalk.realifiedGreenSkew
    (finiteC3SymplecticNaimarkRealization M x)
    (finiteC3SymplecticNaimarkRealization M (Complex.I • y))

/-- Final complex readout, applied only after both real quadratures have been
retained. -/
def FiniteC3SymplecticGreenQuadratures.complexReadout
    (q : FiniteC3SymplecticGreenQuadratures) : ℂ :=
  (q.direct : ℂ) - Complex.I * (q.quarterTurn : ℂ)

theorem finiteC3SymplecticNaimarkGreenQuadratures_direct
    (M : ℕ)
    (x y : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier M) :
    (finiteC3SymplecticNaimarkGreenQuadratures M x y).direct =
      (greenForm (𝕜 := ℂ) x y).re :=
  realifiedGreenSkew_finiteC3SymplecticNaimarkRealization M x y

/-- The second skew reading is the negative imaginary Green quadrature. -/
theorem finiteC3SymplecticNaimarkGreenQuadratures_quarterTurn
    (M : ℕ)
    (x y : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier M) :
    (finiteC3SymplecticNaimarkGreenQuadratures M x y).quarterTurn =
      -(greenForm (𝕜 := ℂ) x y).im := by
  rw [show
      (finiteC3SymplecticNaimarkGreenQuadratures M x y).quarterTurn =
        (greenForm (𝕜 := ℂ) x (Complex.I • y)).re from
      realifiedGreenSkew_finiteC3SymplecticNaimarkRealization
        M x (Complex.I • y)]
  rw [greenForm_smul_right]
  simp

/-- The two real skew channels reconstruct the full complex Green form.
This is an exact finite-cutoff identity before any specialization or limit. -/
theorem finiteC3SymplecticNaimark_complexReadout_eq_greenForm
    (M : ℕ)
    (x y : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier M) :
    (finiteC3SymplecticNaimarkGreenQuadratures M x y).complexReadout =
      greenForm (𝕜 := ℂ) x y := by
  rw [FiniteC3SymplecticGreenQuadratures.complexReadout,
    finiteC3SymplecticNaimarkGreenQuadratures_direct,
    finiteC3SymplecticNaimarkGreenQuadratures_quarterTurn]
  apply Complex.ext <;> simp

/-! ## Genuine C3 specialization and completion -/

/-- The two Naimark quadratures of the mixed Genuine C3 ports at cutoff
`3 M`.  The direct and quarter-turn channels remain separate here. -/
def canonicalC3FiniteMixedSymplecticNaimarkQuadratures
    (M : ℕ) (z w : ℂ) : FiniteC3SymplecticGreenQuadratures :=
  finiteC3SymplecticNaimarkGreenQuadratures (3 * M)
    (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
      (3 * M) w)
    (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
      (3 * M) (reflectedParameter z))

/-- Final complex reconstruction of the two retained Genuine quadratures. -/
def canonicalC3FiniteMixedSymplecticNaimarkGreenReadout
    (M : ℕ) (z w : ℂ) : ℂ :=
  (canonicalC3FiniteMixedSymplecticNaimarkQuadratures M z w).complexReadout

/-- The concrete Naimark readout is exactly the finite mixed radial Green
form, without a zero hypothesis or scalar projection. -/
theorem canonicalC3FiniteMixedSymplecticNaimarkGreenReadout_eq_greenForm
    (M : ℕ) (z w : ℂ) :
    canonicalC3FiniteMixedSymplecticNaimarkGreenReadout M z w =
      greenForm (𝕜 := ℂ)
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
          (3 * M) w)
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
          (3 * M) (reflectedParameter z)) := by
  unfold canonicalC3FiniteMixedSymplecticNaimarkGreenReadout
    canonicalC3FiniteMixedSymplecticNaimarkQuadratures
  exact finiteC3SymplecticNaimark_complexReadout_eq_greenForm _ _ _

/-- The concrete all-cutoff Naimark readout converges to the completed radial
Gram kernel.  All finite states live in the same global Naimark space. -/
theorem canonicalC3FiniteMixedSymplecticNaimarkGreenReadout_tendsto_completed
    {z w : ℂ} (hw : 0 < w.re)
    (hzReflected : 0 < (reflectedParameter z).re) :
    Tendsto
      (fun M : ℕ ↦
        canonicalC3FiniteMixedSymplecticNaimarkGreenReadout M z w)
      atTop
      (nhds
        (canonicalCompletedC3MixedRadialGreenKernel
          z w hw hzReflected)) := by
  exact (finiteC3MixedRadialGreen_tendsto_completed hw hzReflected).congr'
    (Eventually.of_forall fun M ↦
      (canonicalC3FiniteMixedSymplecticNaimarkGreenReadout_eq_greenForm
        M z w).symm)

/-! ## The radial channel of the completed `(F,-F')` ledger -/

/-- Xi-weighted concrete Naimark realization of the finite radial ledger
channel for the actual completed trace pair `(F,-F')`. -/
def canonicalCompletedC3FiniteFNegFPrimeSymplecticRadialReadout
    (M : ℕ) (z w : ℂ) : ℂ :=
  mixedHermitianWeight nativeXiCompletionFactor z w *
    canonicalC3FiniteMixedSymplecticNaimarkGreenReadout M
      (operatorHeightParameter z) (operatorHeightParameter w)

/-- The newly realized symplectic readout is not an auxiliary scalar: it is
literally the radial field of the existing six-channel finite ledger. -/
theorem canonicalCompletedC3FiniteFNegFPrimeSymplecticRadialReadout_eq_ledger
    (M : ℕ) (z w : ℂ) :
    canonicalCompletedC3FiniteFNegFPrimeSymplecticRadialReadout M z w =
      (canonicalCompletedC3FiniteFNegFPrimeMixedChannels M z w).radialGreen := by
  unfold canonicalCompletedC3FiniteFNegFPrimeSymplecticRadialReadout
  rw [canonicalC3FiniteMixedSymplecticNaimarkGreenReadout_eq_greenForm]
  rfl

/-- The weighted concrete symplectic radial channel converges to its
completed Hilbert Gram kernel. -/
theorem canonicalCompletedC3FiniteFNegFPrimeSymplecticRadialReadout_tendsto
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ ↦
        canonicalCompletedC3FiniteFNegFPrimeSymplecticRadialReadout M z w)
      atTop
      (nhds
        (mixedHermitianWeight nativeXiCompletionFactor z w *
          canonicalCompletedC3MixedRadialGreenKernel
            (operatorHeightParameter z) (operatorHeightParameter w)
            hw.1
            (by
              simpa [reflectedParameter] using sub_pos.mpr hz.2))) := by
  exact (finiteFNegFPrimeRadialGreenChannel_tendsto_completed hz hw).congr'
    (Eventually.of_forall fun M ↦
      (canonicalCompletedC3FiniteFNegFPrimeSymplecticRadialReadout_eq_ledger
        M z w).symm)

/-- Concrete candidate global Green readout.  Its Naimark radial and
archimedean/chart channels are combined only at this final readout. -/
def canonicalCompletedC3FiniteFNegFPrimeSymplecticGlobalGreenReadout
    (M : ℕ) (z w : ℂ) : ℂ :=
  canonicalCompletedC3FiniteFNegFPrimeSymplecticRadialReadout M z w +
    canonicalCompletedC3ArchimedeanChartMixedChannel z w

/-- The concrete global Green readout converges to the previously defined
candidate global Green kernel. -/
theorem canonicalCompletedC3FiniteFNegFPrimeSymplecticGlobalGreenReadout_tendsto
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ ↦
        canonicalCompletedC3FiniteFNegFPrimeSymplecticGlobalGreenReadout
          M z w)
      atTop
      (nhds
        (canonicalCompletedC3FNegFPrimeMixedGreenKernel z w hw.1
          (by
            simpa [reflectedParameter] using sub_pos.mpr hz.2))) := by
  have hradial :=
    canonicalCompletedC3FiniteFNegFPrimeSymplecticRadialReadout_tendsto hz hw
  have hchart : Tendsto
      (fun _ : ℕ ↦ canonicalCompletedC3ArchimedeanChartMixedChannel z w)
      atTop
      (nhds (canonicalCompletedC3ArchimedeanChartMixedChannel z w)) :=
    tendsto_const_nhds
  simpa [canonicalCompletedC3FiniteFNegFPrimeSymplecticGlobalGreenReadout,
    canonicalCompletedC3FNegFPrimeMixedGreenKernel] using hradial.add hchart

/-- Exact noncircular frontier for the concrete global skew.  Its limit is
the completed `(F,-F')` Wronskian exactly when the independently retained
structural triple tends to zero.  The theorem introduces no zero hypothesis
and does not assert that the structural limit vanishes. -/
theorem
    canonicalCompletedC3FiniteFNegFPrimeSymplecticGlobalGreenReadout_tendsto_wronskian_iff
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    Tendsto
        (fun M : ℕ ↦
          canonicalCompletedC3FiniteFNegFPrimeSymplecticGlobalGreenReadout
            M z w)
        atTop
        (nhds
          (mixedHermitianWeight canonicalC3ChartFactorHeight z w *
            completedGreenWronskian
              completedNativeOperatorCharacteristic
              (fun u : ℂ ↦ -deriv completedNativeOperatorCharacteristic u)
              z w)) ↔
      Tendsto
        (fun M : ℕ ↦
          canonicalC3FiniteMixedHeightStructuralDefect M
            (operatorHeightParameter z) (operatorHeightParameter w))
        atTop (nhds 0) := by
  have hgreen :=
    canonicalCompletedC3FiniteFNegFPrimeSymplecticGlobalGreenReadout_tendsto
      hz hw
  have hfrontier :=
    completedFNegFPrimeWronskian_eq_globalGreenKernel_iff_structural_tendsto_zero
      hz hw
  constructor
  · intro hwronskian
    exact hfrontier.mp (tendsto_nhds_unique hwronskian hgreen)
  · intro hstructural
    have heq := hfrontier.mpr hstructural
    simpa [heq] using hgreen

end

end CarrySelfAdjointOperator
