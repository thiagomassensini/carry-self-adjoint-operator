import CPFormal.Analytic.CpNativeGprePrimeCarryContraction
import CarrySelfAdjointOperator.CompletedC3KernelMetricCalibration
import CarrySelfAdjointOperator.NativeSourceAllOrderSchur

/-! Calibration of the existing complementary form against the actual native
moments. No source vector is defined by a desired moment or Gram. In
particular, an unchanged unit-norm value state cannot be the zeroth moment
vector. The full finite polarized discrepancy keeps every ordered cross. -/
namespace CarrySelfAdjointOperator.SourceKernelCalibration
open CPFormal.Analytic.Cp
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The existing prime-carry complementary readout, on two independent states.
This is the same form packaged upstream in the newer dependency revision. -/
def complementKernel (X Y : NativeGpreTowerHilbert) : ℝ :=
  inner ℝ X Y - inner ℝ (nativeGprePrimeCarryDefectState X)
    (nativeGprePrimeCarryDefectState Y)

theorem complementKernel_self (X : NativeGpreTowerHilbert) :
    complementKernel X X = ‖X‖^2-‖nativeGprePrimeCarryDefectState X‖^2 := by
  simp [complementKernel]

theorem complementKernel_coercive (X : NativeGpreTowerHilbert) :
    (1/12 : ℝ)*‖X‖^2 ≤ complementKernel X X := by
  rw [complementKernel_self]
  have h := nativeGprePrimeCarryDefectState_norm_sq_le X
  nlinarith

/-- Necessary central normalization, not a choice of a source. -/
theorem central_calibration_norm_bound (X : NativeGpreTowerHilbert)
    (h : complementKernel X X = canonicalCompletedNativeLogDerivativeMoment 0) :
    ‖X‖^2 ≤ 12*canonicalCompletedNativeLogDerivativeMoment 0 ∧ ‖X‖^2 < 3/4 := by
  have hc := complementKernel_coercive X
  have hm := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  rw [h] at hc
  constructor <;> nlinarith

/-- A uniform zeroth mismatch for every unmodified state of squared norm ≥ 1. -/
theorem central_discrepancy_gt_one_fortyeighth
    (X : NativeGpreTowerHilbert) (hX : 1 ≤ ‖X‖^2) :
    (1/48 : ℝ) < complementKernel X X-canonicalCompletedNativeLogDerivativeMoment 0 := by
  have hc := complementKernel_coercive X
  have hm := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  nlinarith

/-- Any real-linear isometry preserves this obstruction. Its hypothesis says
that the RAW value state itself is proposed as the zeroth moment vector. -/
theorem raw_unit_state_isometric_transport_noGo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →ₗᵢ[ℝ] NativeGpreTowerHilbert) (v : E) (hv : 1 ≤ ‖v‖^2) :
    complementKernel (L v) (L v) ≠ canonicalCompletedNativeLogDerivativeMoment 0 := by
  have h := central_discrepancy_gt_one_fortyeighth (L v) (by simpa using hv)
  intro he
  rw [he, sub_self] at h
  norm_num at h

private def carryLinear : NativeGpreTowerHilbert →ₗ[ℝ] PrimeCarryDefectGlobalHilbert where
  toFun := nativeGprePrimeCarryDefectState
  map_add' := by
    intro X Y
    apply lp.ext
    funext p
    change inner ℝ (nativeGpreTowerProfileVector (p : ℕ) 1) (X+Y) •
      primeCriticalCenteredCarryDualAxis p =
      inner ℝ (nativeGpreTowerProfileVector (p : ℕ) 1) X •
        primeCriticalCenteredCarryDualAxis p +
      inner ℝ (nativeGpreTowerProfileVector (p : ℕ) 1) Y •
        primeCriticalCenteredCarryDualAxis p
    rw [inner_add_right, add_smul]
  map_smul' := by
    intro a X
    apply lp.ext
    funext p
    change inner ℝ (nativeGpreTowerProfileVector (p : ℕ) 1) (a • X) •
      primeCriticalCenteredCarryDualAxis p =
      a • (inner ℝ (nativeGpreTowerProfileVector (p : ℕ) 1) X •
        primeCriticalCenteredCarryDualAxis p)
    rw [inner_smul_right, smul_smul]

private theorem carry_synthesis {N : ℕ} (U : Fin N → NativeGpreTowerHilbert)
    (x : Fin N → ℝ) :
    nativeGprePrimeCarryDefectState (∑ i, x i • U i) =
      ∑ i, x i • nativeGprePrimeCarryDefectState (U i) := by
  change carryLinear (∑ i, x i • U i) = ∑ i, x i • carryLinear (U i)
  simp only [map_sum, map_smul]

/-- Both inputs, both finite cutoffs, all ordered crossings. -/
theorem complementKernel_synthesis {N M : ℕ}
    (U : Fin N → NativeGpreTowerHilbert) (V : Fin M → NativeGpreTowerHilbert)
    (x : Fin N → ℝ) (y : Fin M → ℝ) :
    complementKernel (∑ i, x i • U i) (∑ j, y j • V j) =
      ∑ i, ∑ j, x i*y j*complementKernel (U i) (V j) := by
  simp only [complementKernel, carry_synthesis, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial, Finset.sum_sub_distrib,
    mul_sub, Finset.mul_sum]
  congr 1 <;> rw [Finset.sum_comm] <;>
    apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

/-- Difference from the actual canonical moment pairing. Vectors remain input
geometric data; this definition neither constructs nor fits them. -/
def momentKernelDiscrepancy (s : ℕ) (U : ℕ → NativeGpreTowerHilbert)
    (i j : ℕ) : ℝ :=
  complementKernel (U i) (U j)-canonicalCompletedNativeLogDerivativeMoment (i+j+s)

/-- Exact all-dimension identity. No sign or vanishing of the discrepancy is
assumed, and the discrepancy includes all off-diagonal terms. -/
theorem native_energy_eq_complement_sub_discrepancy
    (s N : ℕ) (U : ℕ → NativeGpreTowerHilbert) (x : Fin N → ℝ) :
    sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment s N x =
      complementKernel (∑ i, x i • U i.val) (∑ i, x i • U i.val) -
        ∑ i, ∑ j, x i*x j*momentKernelDiscrepancy s U i.val j.val := by
  rw [complementKernel_synthesis]
  simp only [sourceMomentQuadratic, sourceMomentMatrix, Matrix.mulVec,
    dotProduct, Pi.star_apply, star_trivial, Finset.mul_sum,
    momentKernelDiscrepancy, mul_sub, Finset.sum_sub_distrib]
  have h : (∑ i : Fin N, ∑ j : Fin N,
      x i*(canonicalCompletedNativeLogDerivativeMoment (i.val+j.val+s)*x j)) =
      ∑ i : Fin N, ∑ j : Fin N,
        x i*x j*canonicalCompletedNativeLogDerivativeMoment (i.val+j.val+s) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h]
  ring

/-- Unconditional geometric budget with the full, still uncontrolled defect. -/
theorem native_energy_lower_bound_with_discrepancy
    (s N : ℕ) (U : ℕ → NativeGpreTowerHilbert) (x : Fin N → ℝ) :
    (1/12 : ℝ)*‖∑ i, x i • U i.val‖^2 -
        (∑ i, ∑ j, x i*x j*momentKernelDiscrepancy s U i.val j.val) ≤
      sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment s N x := by
  rw [native_energy_eq_complement_sub_discrepancy]
  exact sub_le_sub_right (complementKernel_coercive _) _

end
end CarrySelfAdjointOperator.SourceKernelCalibration
