import CarrySelfAdjointOperator.FinitePositionalObservableShift
import CarrySelfAdjointOperator.NewtonCarryGreenBridge
import CPFormal.Carry.C2OddCorePushforward

/-! Growing C2 center/leg fibers are distinct from fixed-number chart
refinement. The logarithm of the center induces the existing depth commutator;
the logarithm of a leg has an explicit additional term. -/
namespace CarrySelfAdjointOperator
open scoped Matrix
noncomputable section

/-- Real coordinate of a center with a signed offset. The C2 legs use ±1. -/
def c2FiberPoint (m : ℕ) (ε : ℝ) (k : ℕ) : ℝ := (2 : ℝ)^k * m + ε

/-- The positive leg is the literal natural C2 branch point. -/
theorem c2FiberPoint_plus_eq_nat (m k : ℕ) :
    c2FiberPoint m 1 k = ((2 ^ k * m + 1 : ℕ) : ℝ) := by
  simp [c2FiberPoint]

/-- Keeping positivity avoids replacing integer subtraction by truncated subtraction. -/
theorem c2FiberPoint_minus_eq_nat (m k : ℕ) (hm : 0 < m) :
    c2FiberPoint m (-1) k = ((2 ^ k * m - 1 : ℕ) : ℝ) := by
  have hpos : 0 < 2 ^ k * m := by positivity
  have h : 1 ≤ 2 ^ k * m := hpos
  rw [Nat.cast_sub h]
  simp [c2FiberPoint, sub_eq_add_neg]

theorem c2FiberPoint_succ (m k : ℕ) (ε : ℝ) :
    c2FiberPoint m ε (k + 1) = 2 * c2FiberPoint m ε k - ε := by
  simp only [c2FiberPoint, pow_succ]
  ring

theorem c2FiberPoint_centered (m k : ℕ) (ε : ℝ) :
    c2FiberPoint m ε k - ε = (2 : ℝ)^k * m := by
  simp [c2FiberPoint]

theorem c2FiberPoint_centered_log (m k : ℕ) (hm : 0 < m) (ε : ℝ) :
    Real.log (c2FiberPoint m ε k - ε) =
      (k : ℝ) * Real.log 2 + Real.log m := by
  rw [c2FiberPoint_centered, Real.log_mul (by positivity) (by positivity), Real.log_pow]

theorem c2FiberPoint_centered_log_increment (m k : ℕ) (hm : 0 < m) (ε : ℝ) :
    Real.log (c2FiberPoint m ε (k + 1) - ε) -
      Real.log (c2FiberPoint m ε k - ε) = Real.log 2 := by
  rw [c2FiberPoint_centered_log m (k + 1) hm, c2FiberPoint_centered_log m k hm]
  push_cast
  ring

/-- The leg logarithm retains a correction which is absent from the center logarithm. -/
theorem c2FiberPoint_log_center_defect (m k : ℕ) (hm : 0 < m)
    (ε : ℝ) (hx : c2FiberPoint m ε k ≠ 0) :
    Real.log (c2FiberPoint m ε k) - Real.log (c2FiberPoint m ε k - ε) =
      Real.log (1 + ε / ((2 : ℝ)^k * m)) := by
  rw [c2FiberPoint_centered, ← Real.log_div hx (by positivity)]
  congr 1
  unfold c2FiberPoint
  field_simp

/-- Exact correction to the logarithmic increment when the actual leg is read. -/
theorem c2FiberPoint_log_increment_defect (m k : ℕ) (hm : 0 < m)
    (ε : ℝ) (hx : c2FiberPoint m ε k ≠ 0)
    (hy : c2FiberPoint m ε (k + 1) ≠ 0) :
    Real.log (c2FiberPoint m ε (k + 1)) - Real.log (c2FiberPoint m ε k) =
      Real.log 2 + Real.log (1 + ε / ((2 : ℝ)^(k + 1) * m)) -
        Real.log (1 + ε / ((2 : ℝ)^k * m)) := by
  have h0 := c2FiberPoint_log_center_defect m k hm ε hx
  have h1 := c2FiberPoint_log_center_defect m (k + 1) hm ε hy
  have h2 := c2FiberPoint_centered_log_increment m k hm ε
  linarith

/-- The same sampling matrix transports the growing fiber, with its final sample retained. -/
theorem finiteC2FiberObservable_shift_add_boundary
    (f : ℝ → ℝ) (m N : ℕ) (ε : ℝ) (i : Fin (N + 1)) :
    (finiteDepthShift (N + 1)).mulVec (fun j => f (c2FiberPoint m ε j.val)) i +
      (if i.val = N then f (c2FiberPoint m ε (N + 1)) else 0) =
      f (2 * c2FiberPoint m ε i.val - ε) := by
  simpa only [c2FiberPoint_succ] using
    finiteDepthShift_sample_add_boundary (fun k => f (c2FiberPoint m ε k)) N i

/-- A concrete nonzero log correction on the first right C2 leg of core 1. -/
theorem c2FiberPoint_right_log_defect_pos :
    0 < Real.log (c2FiberPoint 1 1 2) - Real.log (c2FiberPoint 1 1 2 - 1) := by
  rw [c2FiberPoint_log_center_defect 1 2 (by norm_num) 1 (by norm_num [c2FiberPoint])]
  apply Real.log_pos
  norm_num

/-- The actual right leg does not have the centered logarithmic increment. -/
theorem c2FiberPoint_right_log_increment_lt :
    Real.log (c2FiberPoint 1 1 3) - Real.log (c2FiberPoint 1 1 2) < Real.log 2 := by
  norm_num [c2FiberPoint]
  rw [← Real.log_div (by norm_num : (9 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)]
  apply Real.log_lt_log <;> norm_num

/-- The centered logarithm is measured on the actual fiber, not chosen by fitting. -/
def finiteC2FiberCenteredLog (m N : ℕ) (ε : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i => Real.log (c2FiberPoint m ε i.val - ε))

theorem finiteC2FiberCenteredLog_eq_depthLog (m N : ℕ) (hm : 0 < m) (ε : ℝ) :
    finiteC2FiberCenteredLog m N ε =
      finiteDepthLogMultiplication 2 N + Real.log m • (1 : Matrix (Fin N) (Fin N) ℝ) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [finiteC2FiberCenteredLog, finiteDepthLogMultiplication, finiteDepthIndex,
      c2FiberPoint_centered_log m i.val hm, mul_comm]
  · simp [finiteC2FiberCenteredLog, finiteDepthLogMultiplication, finiteDepthIndex,
      h]

/-- The original finite commutator is exactly the one measured along a C2 fiber. -/
theorem finiteC2FiberCenteredLog_commutator (m N : ℕ) (hm : 0 < m) (ε q : ℝ) :
    finiteDepthDifference q N * finiteC2FiberCenteredLog m N ε -
      finiteC2FiberCenteredLog m N ε * finiteDepthDifference q N =
      finiteNativeDepthCommutator 2 q N := by
  rw [finiteC2FiberCenteredLog_eq_depthLog m N hm ε]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul, finiteNativeDepthCommutator]
  abel

/-- The first Newton/Green mode supplies the varying part; the core is a zeroth mode. -/
theorem c2Fiber_centeredLog_amplitude_eq_green_and_seed
    (m k : ℕ) (hm : 0 < m) (ε : ℝ) :
    Real.log (c2FiberPoint m ε k - ε) * CPFormal.Carry.Cp.criticalAmplitude 2 k =
      Real.log 2 * ProjectiveDepth.newtonJet
        (CPFormal.Analytic.Cp.primeCarryAmplitudeRatio 2) 1 k +
      Real.log m * ProjectiveDepth.newtonJet
        (CPFormal.Analytic.Cp.primeCarryAmplitudeRatio 2) 0 k := by
  rw [c2FiberPoint_centered_log m k hm ε,
    ← ProjectiveDepth.newtonJet_zero_eq_criticalAmplitude 2 k]
  simp only [ProjectiveDepth.newtonJet_zero, ProjectiveDepth.newtonJet_one]
  ring

end
end CarrySelfAdjointOperator
