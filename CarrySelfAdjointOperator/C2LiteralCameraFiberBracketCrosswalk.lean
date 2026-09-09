import CarrySelfAdjointOperator.C2AlignedBoxOddCoreCrosswalk
import NativeCarrySpectralWeyl.Camera.FiniteCoefficientBridge
import NativeCarrySpectralWeyl.Camera.Geometry
import NativeCarrySpectralWeyl.Camera.BracketProfileBridge

open scoped BigOperators

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Camera.FiniteBridge
open FiniteNativeCarryOperator

noncomputable section

theorem c2CameraAlignedCenter_eq_oddCoreCenter (j : ℕ) :
    FiniteNativeCarryOperator.Camera.alignedCenter 2 j =
      2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j := by
  rw [alignedCenter_eq_cameraSlope_mul, cameraSlope_two]
  exact c2AlignedCenter_eq_oddCoreCenter j

theorem c2CameraAlignedCenter_eq_c2FiberCenter (j : ℕ) :
    ((FiniteNativeCarryOperator.Camera.alignedCenter 2 j : ℕ) : ℝ) =
      c2FiberPoint (c2AlignedIndexCore j) 0 (c2AlignedIndexDepth j) := by
  rw [c2CameraAlignedCenter_eq_oddCoreCenter]
  simp [c2FiberPoint]

theorem c2CenterStencil_eq_fiberBracketStencil (j : ℕ) :
    centerStencil 2 j =
      centeredBracketStencil
        (2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j) 1 := by
  simp only [centerStencil]
  simp only [if_true]
  rw [c2CameraAlignedCenter_eq_oddCoreCenter]

theorem c2CenterStencil_eq_fiberAtomBracket (j : ℕ) :
    centerStencil 2 j =
      atom (2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j - 1) -
        2 • atom (2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j) +
          atom (2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j + 1) := by
  rw [c2CenterStencil_eq_fiberBracketStencil]
  rfl

theorem c2CenterCoefficient_eq_fiberCoefficient (j n : ℕ) :
    centerCoefficient 2 j n =
      bracketCoefficient
        (2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j) 1 n := by
  change bracketCoefficient (FiniteNativeCarryOperator.Camera.alignedCenter 2 j) 1 n = _
  rw [c2CameraAlignedCenter_eq_oddCoreCenter]

theorem c2CenterStencil_eval_eq_fiberBracket (time : ℝ) (j : ℕ) :
    evalStencil time (centerStencil 2 j) =
      FiniteNativeCarryOperator.Operator.centeredBracket time
        (2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j) 1 := by
  rw [c2CenterStencil_eq_fiberBracketStencil,
    evalStencil_centeredBracketStencil]

def c2FiberLogBracket (m k : ℕ) : ℝ :=
  Real.log (c2FiberPoint m (-1) k) -
    2 * Real.log (c2FiberPoint m 0 k) +
      Real.log (c2FiberPoint m 1 k)

def c2FiberLegDefectSum (m k : ℕ) : ℝ :=
  Real.log (1 + (-1 : ℝ) / ((2 : ℝ)^k * m)) +
    Real.log (1 + (1 : ℝ) / ((2 : ℝ)^k * m))

theorem c2FiberLogBracket_eq_legDefectSum
    (m k : ℕ) (hm : 0 < m) (hc : 1 < 2 ^ k * m) :
    c2FiberLogBracket m k = c2FiberLegDefectSum m k := by
  have hleft := c2FiberPoint_log_center_defect m k hm (-1) (by
    have hcm : (1 : ℝ) < (2 : ℝ)^k * m := by
      exact_mod_cast hc
    unfold c2FiberPoint
    norm_num
    linarith)
  have hright := c2FiberPoint_log_center_defect m k hm 1 (by
    simp [c2FiberPoint]
    positivity)
  have hleftcenter :
      c2FiberPoint m (-1) k - (-1) = (2 : ℝ)^k * m := by
    simp [c2FiberPoint]
  have hrightcenter :
      c2FiberPoint m 1 k - 1 = (2 : ℝ)^k * m := by
    simp [c2FiberPoint]
  have hleft' :
      Real.log (c2FiberPoint m (-1) k) - Real.log ((2 : ℝ)^k * m) =
        Real.log (1 + (-1 : ℝ) / ((2 : ℝ)^k * m)) := by
    calc
      Real.log (c2FiberPoint m (-1) k) - Real.log ((2 : ℝ)^k * m) =
          Real.log (c2FiberPoint m (-1) k) -
            Real.log (c2FiberPoint m (-1) k - (-1)) := by rw [hleftcenter]
      _ = _ := hleft
  have hright' :
      Real.log (c2FiberPoint m 1 k) - Real.log ((2 : ℝ)^k * m) =
        Real.log (1 + (1 : ℝ) / ((2 : ℝ)^k * m)) := by
    calc
      Real.log (c2FiberPoint m 1 k) - Real.log ((2 : ℝ)^k * m) =
          Real.log (c2FiberPoint m 1 k) -
            Real.log (c2FiberPoint m 1 k - 1) := by rw [hrightcenter]
      _ = _ := hright
  dsimp [c2FiberLogBracket, c2FiberLegDefectSum]
  have hcenter : c2FiberPoint m 0 k = (2 : ℝ)^k * m := by
    simp [c2FiberPoint]
  rw [hcenter]
  linarith

theorem c2FiberLogBracket_eq_legDefectSum_expanded
    (m k : ℕ) (hm : 0 < m) (hc : 1 < 2 ^ k * m) :
    Real.log (((2 ^ k * m - 1 : ℕ) : ℝ)) -
        2 * Real.log (((2 ^ k * m : ℕ) : ℝ)) +
          Real.log (((2 ^ k * m + 1 : ℕ) : ℝ)) =
      c2FiberLegDefectSum m k := by
  rw [← c2FiberLogBracket_eq_legDefectSum m k hm hc]
  have hsub :
      (((2 ^ k * m - 1 : ℕ) : ℝ)) = (2 : ℝ)^k * m - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 ^ k * m)]
    norm_num
  have hcenter :
      (((2 ^ k * m : ℕ) : ℝ)) = (2 : ℝ)^k * m := by
    norm_num
  have hadd :
      (((2 ^ k * m + 1 : ℕ) : ℝ)) = (2 : ℝ)^k * m + 1 := by
    norm_num
  simp only [c2FiberLogBracket, c2FiberPoint]
  rw [hsub, hcenter, hadd]
  simp only [sub_eq_add_neg, add_zero]

theorem c2AlignedCameraLogBracket_eq_legDefectSum (j : ℕ) :
    Real.log (((4 * (j + 1) - 1 : ℕ) : ℝ)) -
        2 * Real.log (((4 * (j + 1) : ℕ) : ℝ)) +
          Real.log (((4 * (j + 1) + 1 : ℕ) : ℝ)) =
      c2FiberLegDefectSum (c2AlignedIndexCore j) (c2AlignedIndexDepth j) := by
  have hc : 1 < 2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j := by
    rw [← c2AlignedCenter_eq_oddCoreCenter j]
    omega
  simpa [c2FiberLegDefectSum, c2AlignedCenter_eq_oddCoreCenter] using
    (c2FiberLogBracket_eq_legDefectSum_expanded
      (c2AlignedIndexCore j) (c2AlignedIndexDepth j)
      (c2AlignedIndexCore_pos j) hc)

theorem c2AlignedCameraLogBracket_mul_criticalAmplitude_eq_legDefectSum_mul
    (j : ℕ) :
    CPFormal.Carry.Cp.criticalAmplitude 2 (c2AlignedIndexDepth j) *
        (Real.log (((4 * (j + 1) - 1 : ℕ) : ℝ)) -
          2 * Real.log (((4 * (j + 1) : ℕ) : ℝ)) +
            Real.log (((4 * (j + 1) + 1 : ℕ) : ℝ))) =
      CPFormal.Carry.Cp.criticalAmplitude 2 (c2AlignedIndexDepth j) *
        c2FiberLegDefectSum (c2AlignedIndexCore j) (c2AlignedIndexDepth j) := by
  rw [c2AlignedCameraLogBracket_eq_legDefectSum]

theorem c2FiniteCameraCenterStencil_sum_eq_fiber (M : ℕ) :
    (∑ j ∈ Finset.range M, centerStencil 2 j) =
      ∑ j ∈ Finset.range M,
        centeredBracketStencil
          (2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j) 1 := by
  apply Finset.sum_congr rfl
  intro j hj
  exact c2CenterStencil_eq_fiberBracketStencil j

theorem c2FiniteCameraStencil_eq_seed_add_fiberSum (M : ℕ) :
    finiteStencil 2 M =
      seedStencil 2 +
        ∑ j ∈ Finset.range M,
          centeredBracketStencil
            (2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j) 1 := by
  rw [finiteStencil]
  congr 1
  exact c2FiniteCameraCenterStencil_sum_eq_fiber M

end
end CarrySelfAdjointOperator
