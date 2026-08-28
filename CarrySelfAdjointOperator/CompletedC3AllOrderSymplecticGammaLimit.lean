import CarrySelfAdjointOperator.CompletedC3SymplecticNaimarkVectorLimit
import CarrySelfAdjointOperator.CompletedGammaTwoParameterGreenIdentity
import CarrySelfAdjointOperator.NativeCompletedCenteredReflection
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# All-order symplectic C3 Gamma limit

The fixed three-cell symplectic packing is sufficient for a static Green
readout, but the completed TFVD side is built from the whole `3 * M` tower.
This file feeds that same all-cutoff tower into the logarithmic Gamma field
and passes the source, response, kernel, and boundary readout to their vector
limits.

At every cutoff the Gamma boundary and the static Green readout use the same
permanent camera family.  The remaining difference from the raw completed
Wronskian is therefore split exactly into the dynamic Cauchy-to-static term,
the existing structural channel, and the existing head--tail channel.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace
  RealInnerProductSpace Topology

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

local instance completedC3AllOrderGammaCameraComplexInnerProductSpace :
    InnerProductSpace ℂ RealifiedCameraComplexification :=
  RealHilbertComplexification.instInnerProductSpaceComplexOfReal

local instance completedC3AllOrderGammaNaimarkComplexInnerProductSpace :
    InnerProductSpace ℂ RealifiedNaimarkComplexification :=
  RealHilbertComplexification.instInnerProductSpaceComplexOfReal

/-- Symplectic camera source of the genuine C3 port at cutoff `3 * M`. -/
def canonicalCompletedC3AllCutoffSymplecticGammaCameraSource
    (M : ℕ) (z : ℂ) : CarryGammaComplexCamera :=
  finiteC3SymplecticCameraPacking (3 * M)
    (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
      (3 * M) (operatorHeightParameter z))

/-- The completed all-order source, explicitly viewed in the complex Gamma
camera carrier. -/
def canonicalCompletedC3AllOrderSymplecticGammaCameraSource
    (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    CarryGammaComplexCamera :=
  completedC3SymplecticCameraState
    (operatorHeightParameter z) hzStrip.1

/-- The all-cutoff Gamma sources converge in the common camera Hilbert space
to the already-constructed completed symplectic camera state. -/
theorem canonicalCompletedC3AllCutoffSymplecticGammaCameraSource_tendsto
    {z : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ ↦
        canonicalCompletedC3AllCutoffSymplecticGammaCameraSource M z)
      atTop
      (nhds (completedC3SymplecticCameraState
        (operatorHeightParameter z) hzStrip.1)) := by
  exact (finiteC3GenuineSymplecticCameraPacking_tendsto hzStrip.1).comp
    tendsto_three_mul_atTop

/-- Conjugating the centered height parameter gives exactly the reflected
source used by the mixed C3 Green/Wronskian orientation. -/
theorem canonicalCompletedC3AllCutoffSymplecticGammaCameraSource_conj
    (M : ℕ) (w : ℂ) :
    canonicalCompletedC3AllCutoffSymplecticGammaCameraSource M (conj w) =
      finiteC3SymplecticCameraPacking (3 * M)
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
          (3 * M) (reflectedParameter (operatorHeightParameter w))) := by
  rw [canonicalCompletedC3AllCutoffSymplecticGammaCameraSource,
    operatorHeightParameter_conj_eq_reflectedParameter]

/-- Gamma response of one member of the all-cutoff source tower. -/
def canonicalCompletedC3AllCutoffSymplecticGammaState
    (M : ℕ) (z : ℂ) (hz : z.im ≠ 0) : CarryGammaComplexNaimark :=
  carryGammaComplexState z hz
    (canonicalCompletedC3AllCutoffSymplecticGammaCameraSource M z)

/-- Gamma response of the completed all-order symplectic source. -/
def canonicalCompletedC3AllOrderSymplecticGammaState
    (z : ℂ) (hz : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    CarryGammaComplexNaimark :=
  carryGammaComplexState z hz
    (canonicalCompletedC3AllOrderSymplecticGammaCameraSource z hzStrip)

/-- Continuity of the fixed logarithmic resolvent passes the all-cutoff
source convergence to the Gamma responses themselves. -/
theorem canonicalCompletedC3AllCutoffSymplecticGammaState_tendsto
    {z : ℂ} (hz : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ ↦
        canonicalCompletedC3AllCutoffSymplecticGammaState M z hz)
      atTop
      (nhds (canonicalCompletedC3AllOrderSymplecticGammaState
        z hz hzStrip)) := by
  exact (carryGammaSource z hz).continuous.continuousAt.tendsto.comp
    (canonicalCompletedC3AllCutoffSymplecticGammaCameraSource_tendsto hzStrip)

/-- Positive Gamma kernel at one finite member of the all-cutoff tower. -/
def canonicalCompletedC3AllCutoffSymplecticGammaKernel
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  inner ℂ
    (canonicalCompletedC3AllCutoffSymplecticGammaState M z hz)
    (canonicalCompletedC3AllCutoffSymplecticGammaState M w hw)

/-- Positive Gamma kernel of the completed all-order sources. -/
def canonicalCompletedC3AllOrderSymplecticGammaKernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) : ℂ :=
  inner ℂ
    (canonicalCompletedC3AllOrderSymplecticGammaState z hz hzStrip)
    (canonicalCompletedC3AllOrderSymplecticGammaState w hw hwStrip)

/-- The all-cutoff positive kernels converge by vector convergence in the
single global Gamma Hilbert space. -/
theorem canonicalCompletedC3AllCutoffSymplecticGammaKernel_tendsto
    {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ ↦ canonicalCompletedC3AllCutoffSymplecticGammaKernel
        M z w hz hw)
      atTop
      (nhds (canonicalCompletedC3AllOrderSymplecticGammaKernel
        z w hz hw hzStrip hwStrip)) := by
  exact Filter.Tendsto.inner
    (canonicalCompletedC3AllCutoffSymplecticGammaState_tendsto hz hzStrip)
    (canonicalCompletedC3AllCutoffSymplecticGammaState_tendsto hw hwStrip)

/-- Every finite section of the completed all-order Gamma kernel is positive
semidefinite because all states inhabit the same Gamma Hilbert space. -/
theorem canonicalCompletedC3AllOrderSymplecticGammaKernel_posSemidef
    {ι : Type*} [Finite ι]
    (point : ι → ℂ) (hoffAxis : ∀ i, (point i).im ≠ 0)
    (hstrip : ∀ i, operatorHeightParameter (point i) ∈
      genuineCriticalStrip) :
    (Matrix.of fun i j ↦
      canonicalCompletedC3AllOrderSymplecticGammaKernel
        (point i) (point j) (hoffAxis i) (hoffAxis j)
        (hstrip i) (hstrip j)).PosSemidef := by
  change (Matrix.gram ℂ (fun i ↦
    canonicalCompletedC3AllOrderSymplecticGammaState
      (point i) (hoffAxis i) (hstrip i))).PosSemidef
  exact Matrix.posSemidef_gram ℂ _

/-- Boundary readout of the two all-cutoff Gamma sources. -/
def canonicalCompletedC3AllCutoffSymplecticGammaBoundaryReadout
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  carryGammaPolarizedBoundaryReadout
    (canonicalCompletedC3AllCutoffSymplecticGammaCameraSource M)
    z w hz hw

/-- Boundary readout after completing both all-order sources. -/
def canonicalCompletedC3AllOrderSymplecticGammaBoundaryReadout
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) : ℂ :=
  inner ℂ
      (carryGammaComplexCauchyReadout z hz
        (canonicalCompletedC3AllOrderSymplecticGammaCameraSource z hzStrip))
      (canonicalCompletedC3AllOrderSymplecticGammaCameraSource w hwStrip) -
    inner ℂ
      (canonicalCompletedC3AllOrderSymplecticGammaCameraSource z hzStrip)
      (carryGammaComplexCauchyReadout w hw
        (canonicalCompletedC3AllOrderSymplecticGammaCameraSource w hwStrip))

/-- Hermitian orientation matching the reflected second source of the mixed
C3 Green/Wronskian ledger. -/
def canonicalCompletedC3AllCutoffOrientedSymplecticGammaBoundaryReadout
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  canonicalCompletedC3AllCutoffSymplecticGammaBoundaryReadout
    M z (conj w) hz (by simpa using hw)

/-- Completed Hermitian-oriented Gamma boundary on the exact two sources used
by the mixed C3 Green/Wronskian ledger. -/
def canonicalCompletedC3AllOrderOrientedSymplecticGammaBoundaryReadout
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) : ℂ :=
  canonicalCompletedC3AllOrderSymplecticGammaBoundaryReadout
    z (conj w) hz (by simpa using hw) hzStrip
      (operatorHeightParameter_conj_mem_genuineCriticalStrip hwStrip)

/-- At every cutoff the dynamic boundary is spectral separation times the
positive Gamma kernel of the same two sources. -/
theorem canonicalCompletedC3AllCutoffSymplecticGammaBoundaryReadout_eq_kernel
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3AllCutoffSymplecticGammaBoundaryReadout
        M z w hz hw =
      (w - conj z) *
        canonicalCompletedC3AllCutoffSymplecticGammaKernel M z w hz hw := by
  exact carryGammaPolarizedBoundaryReadout_eq_inner
    (canonicalCompletedC3AllCutoffSymplecticGammaCameraSource M)
    z w hz hw

/-- The same exact Gamma identity holds for the completed all-order source. -/
theorem canonicalCompletedC3AllOrderSymplecticGammaBoundaryReadout_eq_kernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3AllOrderSymplecticGammaBoundaryReadout
        z w hz hw hzStrip hwStrip =
      (w - conj z) *
        canonicalCompletedC3AllOrderSymplecticGammaKernel
          z w hz hw hzStrip hwStrip := by
  have hgreen := carryGammaComplex_twoParameter_greenIdentity
    z w hz hw
    (canonicalCompletedC3AllOrderSymplecticGammaCameraSource z hzStrip)
    (canonicalCompletedC3AllOrderSymplecticGammaCameraSource w hwStrip)
  unfold canonicalCompletedC3AllOrderSymplecticGammaBoundaryReadout
  unfold canonicalCompletedC3AllOrderSymplecticGammaKernel
  unfold canonicalCompletedC3AllOrderSymplecticGammaState
  calc
    inner ℂ
          (carryGammaComplexCauchyReadout z hz
            (canonicalCompletedC3AllOrderSymplecticGammaCameraSource z hzStrip))
          (canonicalCompletedC3AllOrderSymplecticGammaCameraSource w hwStrip) -
        inner ℂ
          (canonicalCompletedC3AllOrderSymplecticGammaCameraSource z hzStrip)
          (carryGammaComplexCauchyReadout w hw
            (canonicalCompletedC3AllOrderSymplecticGammaCameraSource w hwStrip)) =
      -(inner ℂ
          (canonicalCompletedC3AllOrderSymplecticGammaCameraSource z hzStrip)
          (carryGammaComplexCauchyReadout w hw
            (canonicalCompletedC3AllOrderSymplecticGammaCameraSource w hwStrip)) -
        inner ℂ
          (carryGammaComplexCauchyReadout z hz
            (canonicalCompletedC3AllOrderSymplecticGammaCameraSource z hzStrip))
          (canonicalCompletedC3AllOrderSymplecticGammaCameraSource w hwStrip)) := by
        ring
    _ = -((conj z - w) *
        inner ℂ
          (carryGammaComplexState z hz
            (canonicalCompletedC3AllOrderSymplecticGammaCameraSource z hzStrip))
          (carryGammaComplexState w hw
            (canonicalCompletedC3AllOrderSymplecticGammaCameraSource w hwStrip))) := by
      rw [hgreen]
    _ = (w - conj z) *
        inner ℂ
          (carryGammaComplexState z hz
            (canonicalCompletedC3AllOrderSymplecticGammaCameraSource z hzStrip))
          (carryGammaComplexState w hw
            (canonicalCompletedC3AllOrderSymplecticGammaCameraSource w hwStrip)) := by
      ring

/-- The complete all-order Cauchy boundary is the vector limit of the exact
finite-source boundary readouts. -/
theorem canonicalCompletedC3AllCutoffSymplecticGammaBoundaryReadout_tendsto
    {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ ↦
        canonicalCompletedC3AllCutoffSymplecticGammaBoundaryReadout
          M z w hz hw)
      atTop
      (nhds (canonicalCompletedC3AllOrderSymplecticGammaBoundaryReadout
        z w hz hw hzStrip hwStrip)) := by
  rw [canonicalCompletedC3AllOrderSymplecticGammaBoundaryReadout_eq_kernel]
  have hkernel :=
    (show Tendsto (fun _ : ℕ ↦ w - conj z) atTop
        (nhds (w - conj z)) from tendsto_const_nhds).mul
      (canonicalCompletedC3AllCutoffSymplecticGammaKernel_tendsto
        hz hw hzStrip hwStrip)
  exact hkernel.congr' (Eventually.of_forall fun M ↦
    (canonicalCompletedC3AllCutoffSymplecticGammaBoundaryReadout_eq_kernel
      M z w hz hw).symm)

/-- The Hermitian-oriented cutoff boundaries converge with the reflected
source kept explicit. -/
theorem canonicalCompletedC3AllCutoffOrientedSymplecticGammaBoundaryReadout_tendsto
    {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ ↦
        canonicalCompletedC3AllCutoffOrientedSymplecticGammaBoundaryReadout
          M z w hz hw)
      atTop
      (nhds
        (canonicalCompletedC3AllOrderOrientedSymplecticGammaBoundaryReadout
          z w hz hw hzStrip hwStrip)) := by
  exact canonicalCompletedC3AllCutoffSymplecticGammaBoundaryReadout_tendsto
    hz (by simpa using hw) hzStrip
      (operatorHeightParameter_conj_mem_genuineCriticalStrip hwStrip)

/-- The raw Wronskian decomposition uses the same all-cutoff symplectic
camera tower that now feeds the Gamma field. -/
theorem canonicalCompletedC3RawHeightMixedWronskian_eq_allCutoffSymplecticGreen_add_channels
    (M : ℕ) {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3RawHeightMixedWronskian z w =
      canonicalC3FiniteMixedSymplecticNaimarkGreenReadout M
          (operatorHeightParameter z) (operatorHeightParameter w) +
        canonicalC3FiniteMixedHeightStructuralDefect M
          (operatorHeightParameter z) (operatorHeightParameter w) +
        canonicalC3MixedHeightTailCompletionDefect M z w := by
  rw [canonicalC3FiniteMixedSymplecticNaimarkGreenReadout_eq_greenForm]
  exact canonicalCompletedC3RawHeightMixedWronskian_eq_green_add_channels
    M hzStrip hwStrip

/-- Cutoff-by-cutoff comparison after orienting the Gamma source pair exactly
as the reflected static C3 Green pair. -/
theorem canonicalCompletedC3AllCutoffOrientedSymplecticGammaBoundary_sub_rawWronskian
    (M : ℕ) {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3AllCutoffOrientedSymplecticGammaBoundaryReadout
          M z w hz hw -
        canonicalCompletedC3RawHeightMixedWronskian w z =
      (canonicalCompletedC3AllCutoffOrientedSymplecticGammaBoundaryReadout
          M z w hz hw -
        canonicalC3FiniteMixedSymplecticNaimarkGreenReadout M
          (operatorHeightParameter w) (operatorHeightParameter z)) -
        canonicalC3FiniteMixedHeightStructuralDefect M
          (operatorHeightParameter w) (operatorHeightParameter z) -
        canonicalC3MixedHeightTailCompletionDefect M w z := by
  rw [canonicalCompletedC3RawHeightMixedWronskian_eq_allCutoffSymplecticGreen_add_channels
    M hwStrip hzStrip]
  ring

/-- Cutoff-by-cutoff form in the nonoriented Gamma convention used by the
positive divided-slope gate.  The mismatch contains only the dynamic
Gamma-to-static Green term and the two existing completed channels. -/
theorem canonicalCompletedC3AllCutoffSymplecticGammaBoundary_sub_rawWronskian
    (M : ℕ) {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3AllCutoffSymplecticGammaBoundaryReadout
          M z w hz hw -
        canonicalCompletedC3RawHeightMixedWronskian w z =
      (canonicalCompletedC3AllCutoffSymplecticGammaBoundaryReadout
          M z w hz hw -
        canonicalC3FiniteMixedSymplecticNaimarkGreenReadout M
          (operatorHeightParameter w) (operatorHeightParameter z)) -
        canonicalC3FiniteMixedHeightStructuralDefect M
          (operatorHeightParameter w) (operatorHeightParameter z) -
        canonicalC3MixedHeightTailCompletionDefect M w z := by
  rw [canonicalCompletedC3RawHeightMixedWronskian_eq_allCutoffSymplecticGreen_add_channels
    M hwStrip hzStrip]
  ring

end

end CarrySelfAdjointOperator
