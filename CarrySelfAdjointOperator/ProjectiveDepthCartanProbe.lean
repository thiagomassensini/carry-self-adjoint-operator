import CarrySelfAdjointOperator.NewtonCarryGreenBridge

/-!
# Exploratory finite Cartan cell for the Newton depth tower

This probe deliberately separates the order-index operators from the
already-existing depth difference and boundary return.  It is not imported by
the root aggregator yet.
-/

namespace CarrySelfAdjointOperator.ProjectiveDepth

open CPFormal.Analytic.Cp
noncomputable section

/-- Finite order lowering on coefficient vectors. -/
def cartanLoweringNat (R : ℕ) (v : ℕ → ℂ) (i : ℕ) : ℂ :=
  if i < R then v (i + 1) else 0

/-- Finite order raising on coefficient vectors, with divided-power weight. -/
def cartanRaisingNat (R : ℕ) (v : ℕ → ℂ) (i : ℕ) : ℂ :=
  if 0 < i ∧ i ≤ R then (i : ℂ) * v (i - 1) else 0

/-- Order-counting operator. -/
def cartanNumberNat (v : ℕ → ℂ) (i : ℕ) : ℂ := (i : ℂ) * v i

/-- The projected multiplication-by-order operator is number plus raising. -/
def cartanMultiplicationNat (R : ℕ) (v : ℕ → ℂ) (i : ℕ) : ℂ :=
  cartanNumberNat v i + cartanRaisingNat R v i

/-- The finite top-order projection. -/
def cartanTopNat (R : ℕ) (v : ℕ → ℂ) (i : ℕ) : ℂ :=
  if i = R then v i else 0

/-- The finite raising/lowering commutator has a single top-order defect. -/
theorem cartan_commutator_nat (R : ℕ) (v : ℕ → ℂ) {i : ℕ} (hi : i ≤ R) :
    cartanLoweringNat R (cartanRaisingNat R v) i -
        cartanRaisingNat R (cartanLoweringNat R v) i =
      v i - ((R + 1 : ℕ) : ℂ) * cartanTopNat R v i := by
  by_cases htop : i = R
  · subst i
    by_cases hR : R = 0
    · subst R
      simp [cartanLoweringNat, cartanRaisingNat, cartanTopNat]
    · have hRpos : 0 < R := Nat.pos_of_ne_zero hR
      have hR1 : 1 ≤ R := hRpos
      simp [cartanLoweringNat, cartanRaisingNat, cartanTopNat, hR, hR1,
        eq_comm, hi, hRpos]
      ring
  · have hlt : i < R := by omega
    by_cases hzero : i = 0
    · subst i
      have hR : R ≠ 0 := by omega
      have hR1 : 1 ≤ R := by omega
      simp [cartanLoweringNat, cartanRaisingNat, cartanTopNat, hR, hR1,
        eq_comm, hlt]
    · have hpos : 0 < i := Nat.pos_of_ne_zero hzero
      have hltprev : i - 1 < R := by omega
      simp [cartanLoweringNat, cartanRaisingNat, cartanTopNat,
        htop, hpos, hlt, hltprev, hi]
      have hidx2 : i - 1 + 1 = i := by omega
      rw [hidx2]
      ring

/-- Lowering commutes with pointwise addition. -/
theorem cartanLoweringNat_add (R : ℕ) (f g : ℕ → ℂ) (i : ℕ) :
    cartanLoweringNat R (fun j => f j + g j) i =
      cartanLoweringNat R f i + cartanLoweringNat R g i := by
  by_cases h : i < R <;> simp [cartanLoweringNat, h]

/-- The order-counting part contributes one additional lowering term. -/
theorem cartan_number_commutator_nat (R : ℕ) (v : ℕ → ℂ) {i : ℕ} (hi : i ≤ R) :
    cartanLoweringNat R (cartanNumberNat v) i -
        cartanNumberNat (cartanLoweringNat R v) i =
      cartanLoweringNat R v i := by
  by_cases htop : i = R
  · subst i
    by_cases hR : R = 0
    · subst R
      simp [cartanLoweringNat, cartanNumberNat]
    · have hRpos : 0 < R := Nat.pos_of_ne_zero hR
      simp [cartanLoweringNat, cartanNumberNat, hRpos, hi]
  · have hlt : i < R := by omega
    simp [cartanLoweringNat, cartanNumberNat, hlt]
    ring

/-- The raw multiplication-by-order commutator has the discrete shift term. -/
theorem cartan_multiplication_commutator_nat (R : ℕ) (v : ℕ → ℂ) {i : ℕ}
    (hi : i ≤ R) :
    cartanLoweringNat R (cartanMultiplicationNat R v) i -
        cartanMultiplicationNat R (cartanLoweringNat R v) i =
      cartanLoweringNat R v i + v i -
        ((R + 1 : ℕ) : ℂ) * cartanTopNat R v i := by
  unfold cartanMultiplicationNat
  rw [cartanLoweringNat_add]
  calc
    (cartanLoweringNat R (cartanNumberNat v) i +
          cartanLoweringNat R (cartanRaisingNat R v) i) -
        (cartanNumberNat (cartanLoweringNat R v) i +
          cartanRaisingNat R (cartanLoweringNat R v) i) =
      (cartanLoweringNat R (cartanNumberNat v) i -
          cartanNumberNat (cartanLoweringNat R v) i) +
        (cartanLoweringNat R (cartanRaisingNat R v) i -
          cartanRaisingNat R (cartanLoweringNat R v) i) := by ring
    _ = cartanLoweringNat R v i +
          (v i - ((R + 1 : ℕ) : ℂ) * cartanTopNat R v i) := by
      rw [cartan_number_commutator_nat R v hi, cartan_commutator_nat R v hi]
    _ = cartanLoweringNat R v i + v i -
          ((R + 1 : ℕ) : ℂ) * cartanTopNat R v i := by ring

/-- A higher Newton mode is not a two-coordinate boundary return. -/
theorem no_return_eq_newtonCarryVector_succ_succ
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (r : ℕ) :
    ¬ ∃ boundary : ℂ × ℂ,
      carryWeightedVerticalReturn q hqpos.le hq1 boundary =
        newtonCarryVector q hqpos.le hq1 (r + 2) := by
  rintro ⟨boundary, hEq⟩
  have htrace := congrArg (carryWeightedVerticalTrace q) hEq
  have hret : carryWeightedVerticalTrace q
      (carryWeightedVerticalReturn q hqpos.le hq1 boundary) = boundary := by
    have hcomp := carryWeightedVerticalTrace_comp_return q hqpos hq1
    have hpoint := congrArg (fun f => f boundary) hcomp
    simpa using hpoint
  have hnewtrace := carryTrace_newtonCarryVector_succ_succ
    q hqpos.le hq1 r
  rw [hret, hnewtrace] at htrace
  have hboundary : boundary = 0 := htrace
  have hnew_ne : newtonCarryVector q hqpos.le hq1 (r + 2) ≠ 0 := by
    intro hz
    have hzval := congrArg (fun x : CarryVerticalL2 => x (r + 2)) hz
    rw [newtonCarryVector_apply] at hzval
    have hpow : (q : ℂ) ^ (r + 2) = 0 := by
      simpa [newtonJet] using hzval
    exact (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hqpos.ne')) hpow
  rw [hboundary] at hEq
  have hEq0 : (0 : CarryVerticalL2) = newtonCarryVector q hqpos.le hq1 (r + 2) := by
    simpa using hEq
  exact hnew_ne hEq0.symm

#print axioms cartan_commutator_nat
#print axioms cartan_multiplication_commutator_nat
#print axioms no_return_eq_newtonCarryVector_succ_succ

end
end CarrySelfAdjointOperator.ProjectiveDepth
