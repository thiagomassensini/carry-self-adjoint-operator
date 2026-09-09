import CarrySelfAdjointOperator.C2FiberDepthLogTransport
import CPFormal.Carry.C2AlignedBox
import CPFormal.Carry.C2Depth
import CPFormal.Carry.PositionalDecomposition

/-! # Crosswalk from aligned C2 boxes to odd-core fibers

This module reuses the pinned C2 incidence and positional-depth APIs.  It
identifies the aligned center `4 * (j + 1)` with the fiber point
`2 ^ k * m`, where `k = positionalDepth 2 (j + 1) + 2` and `m` is the
remaining odd core.  The logarithmic leg correction remains explicit.
-/

namespace CarrySelfAdjointOperator

open scoped Matrix
open CPFormal.Carry.C2
open CPFormal.Carry.Positional

noncomputable section

/-- The 2-adic depth of the aligned center, including its C2 factor `4`. -/
def c2AlignedIndexDepth (j : ℕ) : ℕ :=
  positionalDepth 2 (j + 1) + 2

/- The quotient after removing the maximal power of `2` from `j + 1`. -/
def c2AlignedIndexCore (j : ℕ) : ℕ :=
  (j + 1) / 2 ^ positionalDepth 2 (j + 1)

theorem c2AlignedIndex_factorization (j : ℕ) :
    j + 1 =
      2 ^ positionalDepth 2 (j + 1) * c2AlignedIndexCore j ∧
      ¬2 ∣ c2AlignedIndexCore j := by
  let r := positionalDepth 2 (j + 1)
  have hr := positionalDepth_spec 2 (j + 1) (by norm_num) (by omega)
  have hdiv : 2 ^ r ∣ j + 1 := hr.1
  have hcancel : (j + 1) / 2 ^ r * 2 ^ r = j + 1 :=
    Nat.div_mul_cancel hdiv
  have hfac : j + 1 = 2 ^ r * ((j + 1) / 2 ^ r) := by
    calc
      j + 1 = (j + 1) / 2 ^ r * 2 ^ r := hcancel.symm
      _ = 2 ^ r * ((j + 1) / 2 ^ r) := by ac_rfl
  have hcore : ¬2 ∣ (j + 1) / 2 ^ r := by
    intro htwo
    rcases htwo with ⟨t, ht⟩
    apply hr.2
    refine ⟨t, ?_⟩
    calc
      j + 1 = 2 ^ r * ((j + 1) / 2 ^ r) := hfac
      _ = 2 ^ r * (2 * t) := by rw [ht]
      _ = 2 ^ (r + 1) * t := by
        simp [pow_succ, Nat.mul_assoc, Nat.mul_comm]
  simpa [c2AlignedIndexCore, r] using And.intro hfac hcore

theorem c2AlignedCenter_eq_oddCoreCenter (j : ℕ) :
    4 * (j + 1) =
      2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j := by
  have hfac := (c2AlignedIndex_factorization j).1
  unfold c2AlignedIndexDepth
  rw [pow_add]
  calc
    4 * (j + 1) = 4 *
        (2 ^ positionalDepth 2 (j + 1) * c2AlignedIndexCore j) := by
          exact congrArg (fun x : ℕ => 4 * x) hfac
    _ = 2 ^ positionalDepth 2 (j + 1) * 2 ^ 2 *
        c2AlignedIndexCore j := by ring

theorem c2AlignedCenter_eq_c2Fiber_center (j : ℕ) :
    ((4 * (j + 1) : ℕ) : ℝ) =
      c2FiberPoint (c2AlignedIndexCore j) 0 (c2AlignedIndexDepth j) := by
  rw [c2AlignedCenter_eq_oddCoreCenter]
  simp [c2FiberPoint]

theorem c2AlignedIndexCore_pos (j : ℕ) :
    0 < c2AlignedIndexCore j := by
  have hcore := (c2AlignedIndex_factorization j).2
  have hm0 : c2AlignedIndexCore j ≠ 0 := by
    intro hm
    apply hcore
    simp [hm]
  omega

theorem c2AlignedIndexCore_odd (j : ℕ) :
    Odd (c2AlignedIndexCore j) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  apply (c2AlignedIndex_factorization j).2
  exact even_iff_two_dvd.mp heven

theorem c2AlignedCenter_padicDepth_eq_fiberDepth (j : ℕ) :
    padicValNat 2 (4 * (j + 1)) = c2AlignedIndexDepth j := by
  have hfac := (c2AlignedIndex_factorization j).1
  have hcore := (c2AlignedIndex_factorization j).2
  have hm0 : c2AlignedIndexCore j ≠ 0 :=
    Nat.ne_of_gt (c2AlignedIndexCore_pos j)
  rw [c2AlignedCenter_eq_oddCoreCenter]
  rw [padicValNat_base_pow_mul (by norm_num) hm0]
  rw [padicValNat.eq_zero_of_not_dvd hcore]
  simp [c2AlignedIndexDepth]

theorem c2LeftIncidence_eq_oddCoreMinus (j : ℕ) :
    (leftIncidence j).1.2 =
      2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j - 1 := by
  have hcenter := c2AlignedCenter_eq_oddCoreCenter j
  change 4 * (j + 1) - 1 = _
  rw [hcenter]

theorem c2RightIncidence_eq_oddCorePlus (j : ℕ) :
    (rightIncidence j).1.2 =
      2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j + 1 := by
  have hcenter := c2AlignedCenter_eq_oddCoreCenter j
  change 4 * (j + 1) + 1 = _
  rw [hcenter]

theorem c2LeftIncidence_effectiveDepth_eq_fiberDepth (j : ℕ) :
    CPFormal.Carry.C2.effectiveDepth (leftIncidence j).1.2 =
      c2AlignedIndexDepth j := by
  have hodd : Odd (leftIncidence j).1.2 := by
    have hleg : (arithmeticOddLeg (2 * j)).1 = (leftIncidence j).1.2 := by
      exact congrArg (fun x : OddLeg => x.1) (arithmeticOddLeg_even j)
    rw [← hleg]
    exact (arithmeticOddLeg (2 * j)).2.2
  have hge : 3 ≤ (leftIncidence j).1.2 := by
    have hleg : (arithmeticOddLeg (2 * j)).1 = (leftIncidence j).1.2 := by
      exact congrArg (fun x : OddLeg => x.1) (arithmeticOddLeg_even j)
    rw [← hleg]
    exact (arithmeticOddLeg (2 * j)).2.1
  rw [effectiveDepth_eq_centerDepth hge hodd]
  have hcenter : adjacentCenter (leftIncidence j).1.2 = 4 * (j + 1) := by
    apply adjacentCenter_unique hge
    · exact (leftIncidence j).2.2.1
    · exact (leftIncidence j).2.2.2
  rw [hcenter]
  exact c2AlignedCenter_padicDepth_eq_fiberDepth j

theorem c2RightIncidence_effectiveDepth_eq_fiberDepth (j : ℕ) :
    CPFormal.Carry.C2.effectiveDepth (rightIncidence j).1.2 =
      c2AlignedIndexDepth j := by
  have hodd : Odd (rightIncidence j).1.2 := by
    have hleg : (arithmeticOddLeg (2 * j + 1)).1 = (rightIncidence j).1.2 := by
      exact congrArg (fun x : OddLeg => x.1) (arithmeticOddLeg_odd j)
    rw [← hleg]
    exact (arithmeticOddLeg (2 * j + 1)).2.2
  have hge : 3 ≤ (rightIncidence j).1.2 := by
    have hleg : (arithmeticOddLeg (2 * j + 1)).1 = (rightIncidence j).1.2 := by
      exact congrArg (fun x : OddLeg => x.1) (arithmeticOddLeg_odd j)
    rw [← hleg]
    exact (arithmeticOddLeg (2 * j + 1)).2.1
  rw [effectiveDepth_eq_centerDepth hge hodd]
  have hcenter : adjacentCenter (rightIncidence j).1.2 = 4 * (j + 1) := by
    apply adjacentCenter_unique hge
    · exact (rightIncidence j).2.2.1
    · exact (rightIncidence j).2.2.2
  rw [hcenter]
  exact c2AlignedCenter_padicDepth_eq_fiberDepth j

theorem c2AlignedCenter_log_eq_fiberDepthLog (j : ℕ) :
    Real.log ((4 * (j + 1) : ℕ) : ℝ) =
      (c2AlignedIndexDepth j : ℝ) * Real.log 2 +
        Real.log (c2AlignedIndexCore j) := by
  have hm := c2AlignedIndexCore_pos j
  rw [c2AlignedCenter_eq_c2Fiber_center]
  simpa [c2FiberPoint] using
    (c2FiberPoint_centered_log (c2AlignedIndexCore j)
      (c2AlignedIndexDepth j) hm 0)

theorem c2AlignedCenter_log_amplitude_eq_green_and_seed (j : ℕ) :
    Real.log ((4 * (j + 1) : ℕ) : ℝ) *
        CPFormal.Carry.Cp.criticalAmplitude 2 (c2AlignedIndexDepth j) =
      Real.log 2 * ProjectiveDepth.newtonJet
          (CPFormal.Analytic.Cp.primeCarryAmplitudeRatio 2) 1
            (c2AlignedIndexDepth j) +
        Real.log (c2AlignedIndexCore j) * ProjectiveDepth.newtonJet
          (CPFormal.Analytic.Cp.primeCarryAmplitudeRatio 2) 0
            (c2AlignedIndexDepth j) := by
  rw [c2AlignedCenter_eq_c2Fiber_center]
  simpa [c2FiberPoint] using
    (c2Fiber_centeredLog_amplitude_eq_green_and_seed
      (c2AlignedIndexCore j) (c2AlignedIndexDepth j)
      (c2AlignedIndexCore_pos j) 0)

theorem c2AlignedLeftLeg_eq_c2FiberPoint_minus (j : ℕ) :
    ((leftIncidence j).1.2 : ℝ) =
      c2FiberPoint (c2AlignedIndexCore j) (-1) (c2AlignedIndexDepth j) := by
  rw [c2LeftIncidence_eq_oddCoreMinus]
  rw [← c2FiberPoint_minus_eq_nat
    (c2AlignedIndexCore j) (c2AlignedIndexDepth j)
    (c2AlignedIndexCore_pos j)]

theorem c2AlignedRightLeg_eq_c2FiberPoint_plus (j : ℕ) :
    ((rightIncidence j).1.2 : ℝ) =
      c2FiberPoint (c2AlignedIndexCore j) 1 (c2AlignedIndexDepth j) := by
  rw [c2RightIncidence_eq_oddCorePlus]
  rw [← c2FiberPoint_plus_eq_nat]

theorem c2AlignedLeftLeg_log_center_defect (j : ℕ) :
    Real.log (c2FiberPoint (c2AlignedIndexCore j) (-1)
        (c2AlignedIndexDepth j)) -
      Real.log (c2FiberPoint (c2AlignedIndexCore j) (-1)
        (c2AlignedIndexDepth j) - (-1)) =
      Real.log (1 + (-1 : ℝ) /
        ((2 : ℝ) ^ c2AlignedIndexDepth j * c2AlignedIndexCore j)) := by
  apply c2FiberPoint_log_center_defect
  · exact c2AlignedIndexCore_pos j
  · have hleg : 0 < (leftIncidence j).1.2 := by
      change 0 < 4 * (j + 1) - 1
      omega
    rw [← c2AlignedLeftLeg_eq_c2FiberPoint_minus]
    exact_mod_cast (Nat.ne_of_gt hleg)

theorem c2AlignedRightLeg_log_center_defect (j : ℕ) :
    Real.log (c2FiberPoint (c2AlignedIndexCore j) 1
        (c2AlignedIndexDepth j)) -
      Real.log (c2FiberPoint (c2AlignedIndexCore j) 1
        (c2AlignedIndexDepth j) - 1) =
      Real.log (1 + (1 : ℝ) /
        ((2 : ℝ) ^ c2AlignedIndexDepth j * c2AlignedIndexCore j)) := by
  apply c2FiberPoint_log_center_defect
  · exact c2AlignedIndexCore_pos j
  · have hleg : 0 < (rightIncidence j).1.2 := by
      change 0 < 4 * (j + 1) + 1
      omega
    rw [← c2AlignedRightLeg_eq_c2FiberPoint_plus]
    exact_mod_cast (Nat.ne_of_gt hleg)

theorem c2LeftIncidenceTerm_eq_fiber
    {R : Type*} [Mul R] (depthWeight : ℕ → R) (value : ℕ → R)
    (j : ℕ) :
    incidenceTerm depthWeight value (leftIncidence j) =
      depthWeight (c2AlignedIndexDepth j) *
        value (2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j - 1) := by
  change depthWeight (padicValNat 2 (4 * (j + 1))) *
      value (4 * (j + 1) - 1) = _
  rw [c2AlignedCenter_padicDepth_eq_fiberDepth,
    c2AlignedCenter_eq_oddCoreCenter]

theorem c2RightIncidenceTerm_eq_fiber
    {R : Type*} [Mul R] (depthWeight : ℕ → R) (value : ℕ → R)
    (j : ℕ) :
    incidenceTerm depthWeight value (rightIncidence j) =
      depthWeight (c2AlignedIndexDepth j) *
        value (2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j + 1) := by
  change depthWeight (padicValNat 2 (4 * (j + 1))) *
      value (4 * (j + 1) + 1) = _
  rw [c2AlignedCenter_padicDepth_eq_fiberDepth,
    c2AlignedCenter_eq_oddCoreCenter]

theorem weighted_reindex_alignedBox_fiber_terms
    {R : Type*} [CommRing R]
    (M : ℕ) (depthWeight : ℕ → R) (value : ℕ → R) :
    (∑ n ∈ alignedOddLegBox M,
        oddLegTerm depthWeight value n) =
      ∑ x ∈ alignedIncidenceBox M,
        incidenceTerm depthWeight value x := by
  exact weighted_reindex_alignedBox M depthWeight value

end
end CarrySelfAdjointOperator
