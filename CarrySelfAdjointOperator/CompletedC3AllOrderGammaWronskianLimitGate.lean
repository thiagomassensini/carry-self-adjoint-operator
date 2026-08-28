import CarrySelfAdjointOperator.CompletedC3AllOrderSymplecticGammaLimit
import Mathlib.Tactic

/-!
# Completed all-order Gamma--Wronskian limit gate

The all-cutoff symplectic Gamma construction already places the dynamic Cauchy
boundary and the static C3 Green readout over one permanent camera tower.  This
file passes their explicit difference to the completed carrier, then combines
it with the independently completed structural and head--tail channels.

The resulting theorem contains no unnamed scalar defect: the total finite
channel expression converges exactly to `Gamma boundary - raw Wronskian`.
The desired sewing is consequently equivalent to this concrete limit being
zero.  Separately, the completed source and its Gamma response are proved
nonzero throughout the off-axis strip, so the positive boundary cannot close
by collapse of the carrier.
-/

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace Topology

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

local instance completedC3AllOrderLimitGateCameraComplexInnerProductSpace :
    InnerProductSpace ℂ RealifiedCameraComplexification :=
  RealHilbertComplexification.instInnerProductSpaceComplexOfReal

local instance completedC3AllOrderLimitGateNaimarkComplexInnerProductSpace :
    InnerProductSpace ℂ RealifiedNaimarkComplexification :=
  RealHilbertComplexification.instInnerProductSpaceComplexOfReal

/-! ## Dynamic-to-static limit -/

/-- Static completed Green readout in the argument orientation of the raw
Wronskian `W(w,z)`. -/
def canonicalCompletedC3AllOrderStaticSymplecticGreenReadout
    (z w : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) : ℂ :=
  canonicalCompletedC3MixedRadialGreenKernel
    (operatorHeightParameter w) (operatorHeightParameter z)
    hzStrip.1
    (by simpa [reflectedParameter] using sub_pos.mpr hwStrip.2)

/-- Finite dynamic Cauchy boundary minus the static Green readout over the same
all-cutoff tower. -/
def canonicalCompletedC3AllCutoffSymplecticGammaDynamicStaticDifference
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  canonicalCompletedC3AllCutoffSymplecticGammaBoundaryReadout M z w hz hw -
    canonicalC3FiniteMixedSymplecticNaimarkGreenReadout M
      (operatorHeightParameter w) (operatorHeightParameter z)

/-- Completed dynamic-to-static difference.  Both terms have independently
constructed vector limits. -/
def canonicalCompletedC3AllOrderSymplecticGammaDynamicStaticDifference
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) : ℂ :=
  canonicalCompletedC3AllOrderSymplecticGammaBoundaryReadout
      z w hz hw hzStrip hwStrip -
    canonicalCompletedC3AllOrderStaticSymplecticGreenReadout
      z w hzStrip hwStrip

/-- The first concrete square passes to the limit without merging its dynamic
and static terms. -/
theorem canonicalCompletedC3AllCutoffSymplecticGammaDynamicStaticDifference_tendsto
    {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ ↦
        canonicalCompletedC3AllCutoffSymplecticGammaDynamicStaticDifference
          M z w hz hw)
      atTop
      (nhds
        (canonicalCompletedC3AllOrderSymplecticGammaDynamicStaticDifference
          z w hz hw hzStrip hwStrip)) := by
  have hgamma :=
    canonicalCompletedC3AllCutoffSymplecticGammaBoundaryReadout_tendsto
      hz hw hzStrip hwStrip
  have hstatic :=
    canonicalC3FiniteMixedSymplecticNaimarkGreenReadout_tendsto_completed
      (z := operatorHeightParameter w)
      (w := operatorHeightParameter z)
      hzStrip.1
      (by simpa [reflectedParameter] using sub_pos.mpr hwStrip.2)
  simpa [canonicalCompletedC3AllCutoffSymplecticGammaDynamicStaticDifference,
    canonicalCompletedC3AllOrderSymplecticGammaDynamicStaticDifference,
    canonicalCompletedC3AllOrderStaticSymplecticGreenReadout] using
      hgamma.sub hstatic

/-! ## Channelwise completion of the total mismatch -/

/-- The completed limit of the structural channel in the orientation of
`W(w,z)`. -/
def canonicalCompletedC3AllOrderStructuralChannelLimit
    (z w : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) : ℂ :=
  canonicalCompletedC3RawHeightMixedWronskian w z -
    canonicalCompletedC3AllOrderStaticSymplecticGreenReadout
      z w hzStrip hwStrip

/-- The retained structural channel converges to its exact completed
Wronskian-minus-static-Green value. -/
theorem canonicalC3FiniteMixedHeightStructuralDefect_tendsto_allOrderLimit
    {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ ↦
        canonicalC3FiniteMixedHeightStructuralDefect M
          (operatorHeightParameter w) (operatorHeightParameter z))
      atTop
      (nhds
        (canonicalCompletedC3AllOrderStructuralChannelLimit
          z w hzStrip hwStrip)) := by
  simpa [canonicalCompletedC3AllOrderStructuralChannelLimit,
    canonicalCompletedC3AllOrderStaticSymplecticGreenReadout] using
      (canonicalC3FiniteMixedHeightStructuralDefect_tendsto
        (z := w) (w := z) hwStrip hzStrip)

/-- The complete finite mismatch, retaining dynamic/static, structural, and
head--tail channels separately. -/
def canonicalCompletedC3AllCutoffSymplecticGammaWronskianChannelDifference
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  canonicalCompletedC3AllCutoffSymplecticGammaDynamicStaticDifference
      M z w hz hw -
    canonicalC3FiniteMixedHeightStructuralDefect M
      (operatorHeightParameter w) (operatorHeightParameter z) -
    canonicalC3MixedHeightTailCompletionDefect M w z

/-- Completed value of the same three explicit channels.  The head--tail
channel is absent only because its independently proved limit is zero. -/
def canonicalCompletedC3AllOrderSymplecticGammaWronskianChannelDifference
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) : ℂ :=
  canonicalCompletedC3AllOrderSymplecticGammaDynamicStaticDifference
      z w hz hw hzStrip hwStrip -
    canonicalCompletedC3AllOrderStructuralChannelLimit z w hzStrip hwStrip

/-- The finite three-channel mismatch converges to its fully completed value. -/
theorem canonicalCompletedC3AllCutoffSymplecticGammaWronskianChannelDifference_tendsto
    {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ ↦
        canonicalCompletedC3AllCutoffSymplecticGammaWronskianChannelDifference
          M z w hz hw)
      atTop
      (nhds
        (canonicalCompletedC3AllOrderSymplecticGammaWronskianChannelDifference
          z w hz hw hzStrip hwStrip)) := by
  have hdynamic :=
    canonicalCompletedC3AllCutoffSymplecticGammaDynamicStaticDifference_tendsto
      hz hw hzStrip hwStrip
  have hstructural :=
    canonicalC3FiniteMixedHeightStructuralDefect_tendsto_allOrderLimit
      hzStrip hwStrip
  have htail := canonicalC3MixedHeightTailCompletionDefect_tendsto_zero
    hwStrip.1 hzStrip.1
  simpa [canonicalCompletedC3AllCutoffSymplecticGammaWronskianChannelDifference,
    canonicalCompletedC3AllOrderSymplecticGammaWronskianChannelDifference] using
      (hdynamic.sub hstructural).sub htail

/-- At every cutoff, the explicit three-channel expression is exactly the
Gamma boundary minus the already completed raw Wronskian. -/
theorem canonicalCompletedC3AllCutoffSymplecticGammaWronskianChannelDifference_eq
    (M : ℕ) {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3AllCutoffSymplecticGammaWronskianChannelDifference
        M z w hz hw =
      canonicalCompletedC3AllCutoffSymplecticGammaBoundaryReadout M z w hz hw -
        canonicalCompletedC3RawHeightMixedWronskian w z := by
  unfold canonicalCompletedC3AllCutoffSymplecticGammaWronskianChannelDifference
    canonicalCompletedC3AllCutoffSymplecticGammaDynamicStaticDifference
  exact
    (canonicalCompletedC3AllCutoffSymplecticGammaBoundary_sub_rawWronskian
      M hz hw hzStrip hwStrip).symm

/-- After completion, no term remains hidden: the channel limit is literally
the desired Gamma--Wronskian difference. -/
theorem canonicalCompletedC3AllOrderSymplecticGammaWronskianChannelDifference_eq
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3AllOrderSymplecticGammaWronskianChannelDifference
        z w hz hw hzStrip hwStrip =
      canonicalCompletedC3AllOrderSymplecticGammaBoundaryReadout
          z w hz hw hzStrip hwStrip -
        canonicalCompletedC3RawHeightMixedWronskian w z := by
  unfold canonicalCompletedC3AllOrderSymplecticGammaWronskianChannelDifference
    canonicalCompletedC3AllOrderSymplecticGammaDynamicStaticDifference
    canonicalCompletedC3AllOrderStructuralChannelLimit
  ring

/-- Exact limit criterion for the requested sewing.  The right side contains
the already constructed finite channels and no new hypothesis. -/
theorem canonicalCompletedC3AllOrderSymplecticGammaBoundary_eq_rawWronskian_iff_tendsto
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3AllOrderSymplecticGammaBoundaryReadout
          z w hz hw hzStrip hwStrip =
        canonicalCompletedC3RawHeightMixedWronskian w z ↔
      Tendsto
        (fun M : ℕ ↦
          canonicalCompletedC3AllCutoffSymplecticGammaWronskianChannelDifference
            M z w hz hw)
        atTop (nhds 0) := by
  have hlimit :=
    canonicalCompletedC3AllCutoffSymplecticGammaWronskianChannelDifference_tendsto
      hz hw hzStrip hwStrip
  rw [canonicalCompletedC3AllOrderSymplecticGammaWronskianChannelDifference_eq]
    at hlimit
  constructor
  · intro hsewing
    rw [hsewing, sub_self] at hlimit
    exact hlimit
  · intro hzero
    have hsub :
        canonicalCompletedC3AllOrderSymplecticGammaBoundaryReadout
              z w hz hw hzStrip hwStrip -
            canonicalCompletedC3RawHeightMixedWronskian w z = 0 :=
      tendsto_nhds_unique hlimit hzero
    exact sub_eq_zero.mp hsub

/-! ## Nondegeneracy of the completed positive carrier -/

/-- Every ordinary Dirichlet-gradient coordinate is nonzero in the open
critical strip. -/
theorem positiveDirichletGradient_ne_zero_of_mem_genuineCriticalStrip
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) (n : ℕ) :
    positiveDirichletGradient s n ≠ 0 := by
  intro hzero
  have hedge := finiteReflectedGradientEdge_re_pos hs n
  simp [finiteReflectedGradientEdge, hzero] at hedge

/-- Hence the completed ordinary gradient state cannot vanish. -/
theorem canonicalCompletedC3DirichletGradientState_ne_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    canonicalCompletedC3DirichletGradientState s hs.1 ≠ 0 := by
  intro hstate
  have hcoordinate := congrArg (fun state : CarryVerticalL2 ↦ state 0) hstate
  simp only [canonicalCompletedC3DirichletGradientState_apply] at hcoordinate
  exact (positiveDirichletGradient_ne_zero_of_mem_genuineCriticalStrip hs 0)
    hcoordinate

/-- The permanent camera synthesis preserves that nonzero ordinary leg. -/
theorem completedC3LegCameraState_dirichletGradient_ne_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    completedC3LegCameraState
        (canonicalCompletedC3DirichletGradientState s hs.1) ≠ 0 := by
  intro hcamera
  apply canonicalCompletedC3DirichletGradientState_ne_zero hs
  apply completedC3GlobalLegCameraIsometry.injective
  simpa [completedC3LegCameraState] using hcamera

/-- The completed symplectic source retains the nonzero second leg. -/
theorem canonicalCompletedC3AllOrderSymplecticGammaCameraSource_ne_zero
    {z : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3AllOrderSymplecticGammaCameraSource z hzStrip ≠ 0 := by
  intro hsource
  have hsnd := congrArg
    (fun source : CarryGammaComplexCamera ↦ source.snd) hsource
  have hzeroSnd : (0 : CarryGammaComplexCamera).snd =
      (0 : CameraHilbert) := by
    change (0 : CameraHilbert) = 0
    rfl
  rw [hzeroSnd] at hsnd
  apply completedC3LegCameraState_dirichletGradient_ne_zero hzStrip
  simpa [canonicalCompletedC3AllOrderSymplecticGammaCameraSource,
    completedC3SymplecticCameraState] using hsnd

/-- Resolvent injectivity carries nondegeneracy to the all-order Gamma state. -/
theorem canonicalCompletedC3AllOrderSymplecticGammaState_ne_zero
    {z : ℂ} (hz : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3AllOrderSymplecticGammaState z hz hzStrip ≠ 0 := by
  intro hstate
  apply canonicalCompletedC3AllOrderSymplecticGammaCameraSource_ne_zero hzStrip
  apply carryGammaSource_injective z hz
  have hgamma :
      carryGammaSource z hz
          (canonicalCompletedC3AllOrderSymplecticGammaCameraSource z hzStrip) =
        carryGammaSource z hz 0 := by
    change carryGammaSource z hz
      (canonicalCompletedC3AllOrderSymplecticGammaCameraSource z hzStrip) = 0
      at hstate
    calc
      carryGammaSource z hz
          (canonicalCompletedC3AllOrderSymplecticGammaCameraSource z hzStrip) =
          0 := hstate
      _ = carryGammaSource z hz 0 := (map_zero _).symm
  exact hgamma

/-- The diagonal all-order Gamma kernel is nonzero. -/
theorem canonicalCompletedC3AllOrderSymplecticGammaKernel_diagonal_ne_zero
    {z : ℂ} (hz : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3AllOrderSymplecticGammaKernel
        z z hz hz hzStrip hzStrip ≠ 0 := by
  unfold canonicalCompletedC3AllOrderSymplecticGammaKernel
  exact inner_self_ne_zero.mpr
    (canonicalCompletedC3AllOrderSymplecticGammaState_ne_zero hz hzStrip)

/-- Consequently the nonoriented diagonal Gamma boundary is nonzero off the
real height axis. -/
theorem canonicalCompletedC3AllOrderSymplecticGammaBoundaryReadout_diagonal_ne_zero
    {z : ℂ} (hz : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3AllOrderSymplecticGammaBoundaryReadout
        z z hz hz hzStrip hzStrip ≠ 0 := by
  rw [canonicalCompletedC3AllOrderSymplecticGammaBoundaryReadout_eq_kernel]
  apply mul_ne_zero
  · apply sub_ne_zero.mpr
    intro hconj
    apply hz
    exact Complex.conj_eq_iff_im.mp hconj.symm
  · exact canonicalCompletedC3AllOrderSymplecticGammaKernel_diagonal_ne_zero
      hz hzStrip

end

end CarrySelfAdjointOperator
