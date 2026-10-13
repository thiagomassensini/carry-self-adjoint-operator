import CarrySelfAdjointOperator.NativeGammaMaterialGraphDefect

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped BigOperators InnerProductSpace ComplexConjugate Matrix
open PhysicalSewing NativeLaguerre
noncomputable section
set_option autoImplicit false

def nativeGammaCameraSource (z : ℂ) (i : Fin 6) : CarryGammaComplexCamera :=
  nativeSixCameraSynthesis (Pi.single i (nativeCanonicalGammaCoefficients z i))

def nativeGammaCameraTrace (z : ℂ) (hz : z.im ≠ 0) (i : Fin 6) : CarryGammaComplexCamera :=
  nativeComplexCauchy z hz (nativeGammaCameraSource z i)

def nativeGammaCameraFirstPort (C : ℕ) (z : ℂ) (i : Fin 6) : Fin (materialCameraWindow C) → ℂ :=
  materialCameraLift C (Pi.single i (nativeCanonicalGammaCoefficients z i))

def nativeGammaCameraSecondPort (C : ℕ) (z : ℂ) (hz : z.im ≠ 0) (i : Fin 6) :
    Fin (materialCameraWindow C) → ℂ :=
  materialCameraLift C (nativeSixCameraCoordinates (nativeGammaCameraTrace z hz i))

def nativeGammaCameraGraphPort (C k : ℕ) (z : ℂ) (i : Fin 6) : Fin (materialCameraWindow C) → ℂ :=
  fun j => radialResponse (materialCameraWindow C) k j * nativeGammaCameraFirstPort C z i j

def nativeGammaCameraDefect (C k : ℕ) (z : ℂ) (hz : z.im ≠ 0) (i : Fin 6) :
    Fin (materialCameraWindow C) → ℂ :=
  nativeGammaCameraSecondPort C z hz i - nativeGammaCameraGraphPort C k z i

theorem sum_cameraCoefficients (c : Fin 6 → ℂ) : (∑ i, Pi.single i (c i)) = c := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem nativeGammaCameraSource_sum (z : ℂ) : ∑ i, nativeGammaCameraSource z i = nativeCanonicalGammaSource z := by
  rw [nativeCanonicalGammaSource_eq_synthesis]
  simp only [nativeGammaCameraSource, ← map_sum, sum_cameraCoefficients]

theorem nativeGammaCameraTrace_sum (z : ℂ) (hz : z.im ≠ 0) :
    ∑ i, nativeGammaCameraTrace z hz i = nativeCanonicalGammaCauchyTrace z hz := by
  simp only [nativeGammaCameraTrace, ← map_sum, nativeGammaCameraSource_sum,
    nativeCanonicalGammaCauchyTrace]

theorem nativeGammaCameraFirstPort_sum (C : ℕ) (z : ℂ) :
    ∑ i, nativeGammaCameraFirstPort C z i = nativeGammaMaterialFirstPort C z := by
  simp only [nativeGammaCameraFirstPort, nativeGammaMaterialFirstPort, ← map_sum, sum_cameraCoefficients]

theorem nativeGammaCameraSecondPort_sum (C : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    ∑ i, nativeGammaCameraSecondPort C z hz i = nativeGammaMaterialSecondPort C z hz := by
  simp only [nativeGammaCameraSecondPort, ← map_sum, nativeGammaCameraTrace_sum,
    nativeGammaMaterialSecondPort]

theorem nativeGammaCameraGraphPort_sum (C k : ℕ) (z : ℂ) :
    ∑ i, nativeGammaCameraGraphPort C k z i =
      (fun j => radialResponse (materialCameraWindow C) k j * nativeGammaMaterialFirstPort C z j) := by
  funext j
  simp only [Finset.sum_apply, nativeGammaCameraGraphPort, ← Finset.mul_sum]
  congr 1
  exact congrFun (nativeGammaCameraFirstPort_sum C z) j

theorem nativeGammaCameraDefect_sum (C k : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    ∑ i, nativeGammaCameraDefect C k z hz i = nativeGammaMaterialGraphDefect C k z hz := by
  simp only [nativeGammaCameraDefect, Finset.sum_sub_distrib, nativeGammaCameraSecondPort_sum,
    nativeGammaCameraGraphPort_sum, nativeGammaMaterialGraphDefect, secondPortDefect]

theorem twoPortSynthesis_sum {ι : Type*} [Fintype ι] (N k : ℕ)
    (v s : ι → Fin N → ℂ) :
    twoPortSynthesis N k (∑ i, v i) (∑ i, s i) = ∑ i, twoPortSynthesis N k (v i) (s i) := by
  unfold twoPortSynthesis twoPortReconstruct
  apply Prod.ext
  · simp [Prod.fst_sum, map_sum, Finset.smul_sum, Finset.sum_add_distrib]
  · simp [Prod.snd_sum, map_sum, Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]

theorem nativeGammaCameraWholePair_sum (C k : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    ∑ i, twoPortSynthesis (materialCameraWindow C) k (nativeGammaCameraFirstPort C z i)
      (nativeGammaCameraSecondPort C z hz i) =
    twoPortSynthesis (materialCameraWindow C) k (nativeGammaMaterialFirstPort C z)
      (nativeGammaMaterialSecondPort C z hz) := by
  rw [← twoPortSynthesis_sum, nativeGammaCameraFirstPort_sum, nativeGammaCameraSecondPort_sum]

theorem nativeGammaCameraDefects_faithful (C k : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    (∀ i a, mixedPhysicalProbes (materialCameraWindow C) k (radialResponse (materialCameraWindow C) k)
      (nativeGammaCameraDefect C k z hz i) a = 0) ↔ ∀ i, nativeGammaCameraDefect C k z hz i = 0 :=
  cameraDefectFamily_faithful _ _ _ _

theorem nativeGammaMaterialProbes_headTail (C k R : ℕ) (z : ℂ) (hz : z.im ≠ 0)
    (a : Fin (materialCameraWindow C)) :
    nativeGammaMaterialProbes C k z hz a = mixedProbeScale k *
      ((∑ r : Fin (R+1), (feature r.val a.val : ℂ) *
        laguerreReadout r.val (nativeGammaMaterialGraphDefect C k z hz)) +
      matrixPairing (cauchyMatrix (materialCameraWindow C))
        (tailDiagonal R (materialCameraWindow C) *ᵥ Pi.single a 1)
        (tailDiagonal R (materialCameraWindow C) *ᵥ nativeGammaMaterialGraphDefect C k z hz)) :=
  mixedPhysicalProbes_tail_as_originalGram _ _ _ _ _ _

theorem nativeGammaCamera_fourHeadTails (C k R : ℕ) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedNativeProjectiveChiralForm
      (∑ i, twoPortSynthesis (materialCameraWindow C) k (nativeGammaCameraFirstPort C z i)
        (nativeGammaCameraGraphPort C k z i + nativeGammaCameraDefect C k z hz i))
      (∑ j, twoPortSynthesis (materialCameraWindow C) k (nativeGammaCameraFirstPort C w j)
        (nativeGammaCameraGraphPort C k w j + nativeGammaCameraDefect C k w hw j)) =
    ∑ i, ∑ j,
      (twoPortPolarizedHeadTail (materialCameraWindow C) k R (nativeGammaCameraFirstPort C z i)
        (nativeGammaCameraGraphPort C k z i) (nativeGammaCameraFirstPort C w j) (nativeGammaCameraGraphPort C k w j) +
      twoPortPolarizedHeadTail (materialCameraWindow C) k R (nativeGammaCameraFirstPort C z i)
        (nativeGammaCameraGraphPort C k z i) 0 (nativeGammaCameraDefect C k w hw j) +
      twoPortPolarizedHeadTail (materialCameraWindow C) k R 0 (nativeGammaCameraDefect C k z hz i)
        (nativeGammaCameraFirstPort C w j) (nativeGammaCameraGraphPort C k w j) +
      twoPortPolarizedHeadTail (materialCameraWindow C) k R 0 (nativeGammaCameraDefect C k z hz i)
        0 (nativeGammaCameraDefect C k w hw j)) :=
  twoPort_camera_defect_fourHeadTails _ _ _ _ _ _ _ _ _

end
end CarrySelfAdjointOperator.GammaMaterialSewing
