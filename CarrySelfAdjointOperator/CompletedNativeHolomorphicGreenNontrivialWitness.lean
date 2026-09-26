import CarrySelfAdjointOperator.CompletedNativeHolomorphicGreenTfvdFourChannel
import Mathlib.Tactic

/-!
# A nontrivial camera-pair witness for the holomorphic C3 Green polarization

At the spectral centre the direct `w` and independent `reflectedZ` ordinary
roles have the same parameter. This file proves that their finite camera
atlas has a nonzero reconstructed state (under the explicit lossless-TFVD
assumption `0 < q`), and therefore that at least one holomorphic camera-pair
first jet is nonzero. The argument concerns the holomorphic polarization;
it does not alter the diagonal undressed port.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section
set_option autoImplicit false

/-! ## The central ordinary camera states -/

/-- The direct and reflected ordinary roles use the same central parameter.
This is an equality of reconstructed camera states, not an identification of
their source-role labels away from the centre. -/
theorem canonicalC3CameraResolvedHolomorphicCenterState_direct_eq_reflected
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) (camera : ℕ) :
    canonicalC3CameraResolvedHolomorphicDirectCenterState
        M q hq0 hq1 S u camera =
      canonicalC3CameraResolvedHolomorphicReflectedCenterState
        M q hq0 hq1 S u camera := by
  rfl

/-- The finite fixed-atlas aggregate of the central direct ordinary legs. -/
def canonicalC3HolomorphicDirectCenterAtlasState
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) : CarryVerticalL2 :=
  ∑ camera ∈ canonicalFiniteCameraAtlas M,
    canonicalC3CameraResolvedHolomorphicDirectCenterState
      M q hq0 hq1 S u camera

/-- The finite fixed-atlas aggregate of the central reflected ordinary legs. -/
def canonicalC3HolomorphicReflectedCenterAtlasState
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) : CarryVerticalL2 :=
  ∑ camera ∈ canonicalFiniteCameraAtlas M,
    canonicalC3CameraResolvedHolomorphicReflectedCenterState
      M q hq0 hq1 S u camera

/-- At the centre the two aggregate source states agree role-by-role. -/
theorem canonicalC3HolomorphicCenterAtlasState_direct_eq_reflected
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) :
    canonicalC3HolomorphicDirectCenterAtlasState M q hq0 hq1 S u =
      canonicalC3HolomorphicReflectedCenterAtlasState M q hq0 hq1 S u := by
  unfold canonicalC3HolomorphicDirectCenterAtlasState
    canonicalC3HolomorphicReflectedCenterAtlasState
  apply Finset.sum_congr rfl
  intro camera _
  exact canonicalC3CameraResolvedHolomorphicCenterState_direct_eq_reflected
    M q hq0 hq1 S u camera

/-! ## Canonical reconstruction of the central ordinary prefix -/

/-- The independent-reflected canonical reconstruction at `(0,0)` is the
ordinary/log-jet three-prefix source at the common central parameter. -/
theorem canonicalC3IndependentReflectedSixSourceReconstruction_center_eq_prefix
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3IndependentReflectedSixSourceReconstruction
        M q hqpos.le hq1 S 0 0 =
      canonicalC3AllCutoffMixedSourcePrefixState M
        (operatorHeightParameter 0) (operatorHeightParameter 0) := by
  unfold canonicalC3IndependentReflectedSixSourceReconstruction
  calc
    canonicalC3AllCutoffMixedSourceTfvdReconstruction q hqpos.le hq1 S
        (nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected
          M q S 0 0) =
      canonicalC3AllCutoffMixedSourceTfvdReconstruction q hqpos.le hq1 S
        (nativeC3SeededClockTfvdSixSourceAnalysis M q S
          (operatorHeightParameter 0) (operatorHeightParameter 0)) := by
        congr 1
        simpa using
          (nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected_physicalSection
            M q S 0)
    _ = canonicalC3AllCutoffMixedSourcePrefixState M
          (operatorHeightParameter 0) (operatorHeightParameter 0) :=
      canonicalC3AllCutoffMixedSourceTfvdReconstruction_seededClockAnalysis
        M (operatorHeightParameter 0) (operatorHeightParameter 0) q hqpos hq1 S

/-- Zero extension of the canonical central finite direct leg is precisely
the ordinary Dirichlet-gradient prefix at cutoff `3 * M`. -/
theorem canonicalC3IndependentReflectedUndressedDirectCenterState_eq_prefix
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    finiteC3LegL2Extension (3 * M)
      (canonicalC3IndependentReflectedUndressedDirectGreenPort
        M q hqpos.le hq1 S 0 0).1 =
      canonicalCompletedC3DirichletGradientPrefixState
        (operatorHeightParameter 0) (3 * M) := by
  unfold canonicalC3IndependentReflectedUndressedDirectGreenPort
  rw [canonicalC3IndependentReflectedSixSourceReconstruction_center_eq_prefix
    M q hqpos hq1 S]
  ext n
  rw [finiteC3LegL2Extension_apply,
    canonicalCompletedC3DirichletGradientPrefixState_apply]
  by_cases hn : n < 3 * M
  · simp [hn, undressedGreenPort,
      CanonicalC3AllCutoffMixedSourceHilbert.wSource,
      canonicalC3AllCutoffMixedSourcePrefixState,
      canonicalCompletedC3HilbertPrefixState]
  · simp [hn]

/-- The central canonical ordinary prefix has a concrete nonzero coordinate
whenever the material cutoff contains the initial C3 block. -/
theorem canonicalC3HolomorphicCenterPrefix_ne_zero
    (M : ℕ) (hM : 0 < M) :
    canonicalCompletedC3DirichletGradientPrefixState
      (operatorHeightParameter 0) (3 * M) ≠ 0 := by
  intro hzero
  have hcoordinate := congrArg (fun state : CarryVerticalL2 => state 0) hzero
  rw [canonicalCompletedC3DirichletGradientPrefixState_apply,
    if_pos (by omega : 0 < 3 * M)] at hcoordinate
  exact positiveDirichletGradient_operatorHeight_zero_ne_zero hcoordinate

/-! ## Extraction of a nonzero holomorphic camera-pair first jet -/

/-- The canonical finite direct central leg is nonzero as soon as the first
C3 block is present. -/
theorem canonicalC3IndependentReflectedUndressedDirectCenterLeg_ne_zero
    (M : ℕ) (hM : 0 < M) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    (canonicalC3IndependentReflectedUndressedDirectGreenPort
      M q hqpos.le hq1 S 0 0).1 ≠ 0 := by
  intro hzero
  have hextzero : finiteC3LegL2Extension (3 * M)
      (canonicalC3IndependentReflectedUndressedDirectGreenPort
        M q hqpos.le hq1 S 0 0).1 = 0 := by
    change finiteC3LegL2ExtensionIsometry (3 * M)
      (canonicalC3IndependentReflectedUndressedDirectGreenPort
        M q hqpos.le hq1 S 0 0).1 = 0
    rw [hzero, map_zero]
  rw [canonicalC3IndependentReflectedUndressedDirectCenterState_eq_prefix
    M q hqpos hq1 S] at hextzero
  exact canonicalC3HolomorphicCenterPrefix_ne_zero M hM hextzero

/-- A nonzero finite canonical leg forces a nonzero direct camera leg. This
uses only the existing fixed-atlas port synthesis, not an enumeration of the
atlas. -/
theorem exists_canonicalC3CameraResolvedHolomorphicDirectCenterState_ne_zero
    (M : ℕ) (hM : 0 < M) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ∃ camera ∈ canonicalFiniteCameraAtlas M,
      canonicalC3CameraResolvedHolomorphicDirectCenterState
        M q hqpos.le hq1 S 0 camera ≠ 0 := by
  by_contra h
  push Not at h
  let directPort : ℕ → NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier (3 * M) :=
    fun camera => cameraResolvedIndependentReflectedUndressedDirectGreenPort
      M q hqpos.le hq1 S 0 0 camera
  have hleg (camera : ℕ) (hcamera : camera ∈ canonicalFiniteCameraAtlas M) :
      (directPort camera).1 = 0 := by
    apply (finiteC3LegL2ExtensionIsometry (3 * M)).injective
    change finiteC3LegL2Extension (3 * M) (directPort camera).1 =
      finiteC3LegL2Extension (3 * M) 0
    have hstate := h camera hcamera
    change finiteC3LegL2Extension (3 * M) (directPort camera).1 = 0 at hstate
    have hextzero : finiteC3LegL2Extension (3 * M)
        (0 : NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace (3 * M)) = 0 := by
      change finiteC3LegL2ExtensionIsometry (3 * M) 0 = 0
      exact map_zero _
    rw [hextzero]
    exact hstate
  have hsum :
      ∑ camera ∈ canonicalFiniteCameraAtlas M, (directPort camera).1 = 0 := by
    apply Finset.sum_eq_zero
    exact hleg
  have hports := cameraResolvedIndependentReflectedUndressedDirectGreenPort_sum_eq_canonical
    M q hqpos.le hq1 S 0 0
  have hfirstMap :
      (∑ camera ∈ canonicalFiniteCameraAtlas M, directPort camera).1 =
        ∑ camera ∈ canonicalFiniteCameraAtlas M, (directPort camera).1 := by
    have hmap := map_sum (AddMonoidHom.fst _ _) directPort
      (canonicalFiniteCameraAtlas M)
    change
      (∑ camera ∈ canonicalFiniteCameraAtlas M, directPort camera).1 =
        ∑ camera ∈ canonicalFiniteCameraAtlas M, (directPort camera).1 at hmap
    exact hmap
  have hcanonical :
      (canonicalC3IndependentReflectedUndressedDirectGreenPort
        M q hqpos.le hq1 S 0 0).1 = 0 := by
    calc
      (canonicalC3IndependentReflectedUndressedDirectGreenPort
        M q hqpos.le hq1 S 0 0).1 =
          (∑ camera ∈ canonicalFiniteCameraAtlas M, directPort camera).1 :=
        (congrArg Prod.fst hports).symm
      _ = ∑ camera ∈ canonicalFiniteCameraAtlas M, (directPort camera).1 := hfirstMap
      _ = 0 := hsum
  exact canonicalC3IndependentReflectedUndressedDirectCenterLeg_ne_zero
    M hM q hqpos hq1 S hcanonical

/-- At least one oriented direct/reflected central camera pairing is nonzero.
The witness is same-camera because the two reconstructed ordinary roles agree
at the central reflected coordinate. No conclusion is made about other pairs. -/
theorem exists_cameraPair_holomorphicCenterInner_ne_zero
    (M : ℕ) (hM : 0 < M) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ∃ directCamera ∈ canonicalFiniteCameraAtlas M,
      ∃ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
        inner ℂ
          (canonicalC3CameraResolvedHolomorphicDirectCenterState
            M q hqpos.le hq1 S 0 directCamera)
          (canonicalC3CameraResolvedHolomorphicReflectedCenterState
            M q hqpos.le hq1 S 0 reflectedCamera) ≠ 0 := by
  rcases exists_canonicalC3CameraResolvedHolomorphicDirectCenterState_ne_zero
    M hM q hqpos hq1 S with ⟨camera, hcamera, hstate⟩
  refine ⟨camera, hcamera, camera, hcamera, ?_⟩
  rw [canonicalC3CameraResolvedHolomorphicCenterState_direct_eq_reflected]
  exact inner_self_ne_zero.mpr hstate

/-- The holomorphic eigenvalue polarization has a nonzero first jet for some
camera pair in every nonempty material atlas. The witness is same-camera
only because the two *central* ordinary source roles agree; no such equality
is asserted away from the centre. -/
theorem exists_cameraPair_holomorphicGreenFirstJet_ne_zero
    (M : ℕ) (hM : 0 < M) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ∃ directCamera ∈ canonicalFiniteCameraAtlas M,
      ∃ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
        canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenJetCoefficient
          M q hqpos.le hq1 S 0 directCamera reflectedCamera 1 ≠ 0 := by
  rcases exists_cameraPair_holomorphicCenterInner_ne_zero
    M hM q hqpos hq1 S with
      ⟨directCamera, hdirect, reflectedCamera, hreflected, hinner⟩
  refine ⟨directCamera, hdirect, reflectedCamera, hreflected, ?_⟩
  rw [canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenJetCoefficient_one_eq_scaledCentralInner,
    canonicalC3CameraResolvedHolomorphicCentralInner_eq_tfvdInner]
  exact mul_ne_zero holomorphicC3Eigenvalue_deriv_zero_ne_zero hinner

/-- For the same witness pair, the complete reconstructed four-channel TFVD
pairing is nonzero. This does not assert nonvanishing of any individual
channel. -/
theorem exists_cameraPair_holomorphicGreenTfvdFourChannel_ne_zero
    (M : ℕ) (hM : 0 < M) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ∃ directCamera ∈ canonicalFiniteCameraAtlas M,
      ∃ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
        (inner ℂ
          (canonicalC3CameraResolvedHolomorphicDirectGreenChannel
            M q hqpos.le hq1 S 0 directCamera)
          (canonicalC3CameraResolvedHolomorphicReflectedGreenChannel
            M q hqpos.le hq1 S 0 reflectedCamera) +
        inner ℂ
          (canonicalC3CameraResolvedHolomorphicDirectGreenChannel
            M q hqpos.le hq1 S 0 directCamera)
          (canonicalC3CameraResolvedHolomorphicReflectedReturnChannel
            M q hqpos.le hq1 S 0 reflectedCamera) +
        inner ℂ
          (canonicalC3CameraResolvedHolomorphicDirectReturnChannel
            M q hqpos.le hq1 S 0 directCamera)
          (canonicalC3CameraResolvedHolomorphicReflectedGreenChannel
            M q hqpos.le hq1 S 0 reflectedCamera) +
        inner ℂ
          (canonicalC3CameraResolvedHolomorphicDirectReturnChannel
            M q hqpos.le hq1 S 0 directCamera)
          (canonicalC3CameraResolvedHolomorphicReflectedReturnChannel
            M q hqpos.le hq1 S 0 reflectedCamera)) ≠ 0 := by
  rcases exists_cameraPair_holomorphicGreenFirstJet_ne_zero
    M hM q hqpos hq1 S with
      ⟨directCamera, hdirect, reflectedCamera, hreflected, hjet⟩
  refine ⟨directCamera, hdirect, reflectedCamera, hreflected, ?_⟩
  intro hfour
  apply hjet
  rw [canonicalC3CameraResolvedHolomorphicGreenFirstJet_eq_tfvdFourChannel,
    hfour, mul_zero]

/-- A nonzero first coefficient prevents the corresponding holomorphic
camera-pair kernel from being the zero function. This is a pointwise
differential contradiction, not an analytic-continuation argument. -/
theorem exists_cameraPair_holomorphicGreenKernel_ne_zero
    (M : ℕ) (hM : 0 < M) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ∃ directCamera ∈ canonicalFiniteCameraAtlas M,
      ∃ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
        (fun v =>
          canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel
            M q hqpos.le hq1 S 0 v directCamera reflectedCamera) ≠ 0 := by
  rcases exists_cameraPair_holomorphicGreenFirstJet_ne_zero
    M hM q hqpos hq1 S with
      ⟨directCamera, hdirect, reflectedCamera, hreflected, hjet⟩
  refine ⟨directCamera, hdirect, reflectedCamera, hreflected, ?_⟩
  intro hkernel
  apply hjet
  unfold canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenJetCoefficient
  rw [hkernel]
  simp

end

end CarrySelfAdjointOperator
