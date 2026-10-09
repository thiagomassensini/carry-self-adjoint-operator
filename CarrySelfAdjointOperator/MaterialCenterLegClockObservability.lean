import CarrySelfAdjointOperator.FiniteMaterialClockJets
import Mathlib.LinearAlgebra.Vandermonde
import CPFormal.Analytic.CpBracketConvergence

/-!
# Local material-clock observability of center/leg brackets

The material positions and the bracket weights determine every coefficient.
Clock orders are powers of the existing diagonal material logarithm, without
spectral fitting or a new metric. This is finite local observability only.
It supplies no sign for a completed source or return energy.
-/
namespace CarrySelfAdjointOperator
open CPFormal.Analytic.Cp
open scoped BigOperators
noncomputable section
set_option autoImplicit false

/-- Restriction of the material log clock to a finite list of material nodes. -/
def localMaterialLogClock {N : ℕ} (nodes : Fin N → ℕ) :
    (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) where
  toFun f i := (Real.log (nodes i : ℝ) : ℂ) * f i
  map_add' f g := by funext i; simp [mul_add]
  map_smul' a f := by funext i; simp [mul_left_comm]

/-- Coordinate provenance in the existing full finite material generator.
Material node m is its coordinate m-1, not a depth or a camera label. -/
theorem localMaterialLogClock_restriction {N M : ℕ} (nodes : Fin N → ℕ)
    (hpos : ∀ i, 0 < nodes i) (hcut : ∀ i, nodes i ≤ M)
    (f : FiniteRealSpectralHilbert M) :
    localMaterialLogClock nodes
        (fun i => f ⟨nodes i - 1, by have := hpos i; have := hcut i; omega⟩) =
      fun i => FiniteClockJets.finiteMaterialClock M f
        ⟨nodes i - 1, by have := hpos i; have := hcut i; omega⟩ := by
  funext i
  have hi : nodes i - 1 + 1 = nodes i := by have := hpos i; omega
  simp [localMaterialLogClock, FiniteClockJets.finiteMaterialClock,
    finiteRealSpectralFrequency, hi]

/-- Material diagonal masks commute with the material clock. In particular this
covers any Haar/parity mask specified at these same material nodes. It asserts
no commutation for a bracket or for a reinterpreted camera/depth coordinate. -/
theorem localMaterialLogClock_mask {N : ℕ} (nodes : Fin N → ℕ)
    (mask : Fin N → ℂ) (f : Fin N → ℂ) :
    localMaterialLogClock nodes (fun i => mask i * f i) =
      fun i => mask i * localMaterialLogClock nodes f i := by
  funext i
  change (Real.log (nodes i : ℝ) : ℂ) * (mask i * f i) =
    mask i * ((Real.log (nodes i : ℝ) : ℂ) * f i)
  ring

/-- All local readouts are taken after the full finite clocked synthesis. -/
def materialBracketClockJet {N : ℕ} (nodes : Fin N → ℕ)
    (weights : Fin N → ℂ) : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) where
  toFun f order := ∑ i, weights i * (Real.log (nodes i : ℝ) : ℂ) ^ order.val * f i
  map_add' f g := by funext order; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext order
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The formula is literally bracket applied to powers of the local restriction
of the existing material generator. No differential-order phase is suppressed. -/
theorem materialBracketClockJet_eq_clockPower {N : ℕ} (nodes : Fin N → ℕ)
    (weights : Fin N → ℂ) (f : Fin N → ℂ) (order : Fin N) :
    materialBracketClockJet nodes weights f order =
      ∑ i, weights i * ((localMaterialLogClock nodes ^ order.val) f) i := by
  have hp (r : ℕ) (i : Fin N) :
      ((localMaterialLogClock nodes ^ r) f) i =
        (Real.log (nodes i : ℝ) : ℂ) ^ r * f i := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [pow_succ']
      change (Real.log (nodes i : ℝ) : ℂ) *
        ((localMaterialLogClock nodes ^ r) f) i = _
      rw [ih, pow_succ]
      ring
  simp only [materialBracketClockJet, LinearMap.coe_mk, AddHom.coe_mk, hp, mul_assoc]

/-- Weighted Vandermonde recovery: distinct positive material nodes and nonzero
geometric bracket weights suffice. Mathlib supplies the determinant argument. -/
theorem materialBracketClockJet_injective {N : ℕ} (nodes : Fin N → ℕ)
    (weights : Fin N → ℂ) (hpos : ∀ i, 0 < nodes i)
    (hnodes : Function.Injective nodes) (hweights : ∀ i, weights i ≠ 0) :
    Function.Injective (materialBracketClockJet nodes weights) := by
  have hf : Function.Injective (fun i => (Real.log (nodes i : ℝ) : ℂ)) := by
    intro i j hij
    apply hnodes
    have hlog := Complex.ofReal_injective hij
    have hreal := Real.strictMonoOn_log.injOn
      (show (nodes i : ℝ) ∈ Set.Ioi 0 by change (0 : ℝ) < nodes i; exact_mod_cast hpos i)
      (show (nodes j : ℝ) ∈ Set.Ioi 0 by change (0 : ℝ) < nodes j; exact_mod_cast hpos j) hlog
    exact_mod_cast hreal
  intro x y hxy
  have hz : (fun i => weights i * (x i - y i)) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf
    intro order
    have ho := congrFun hxy order
    change (∑ i, weights i * (Real.log (nodes i : ℝ) : ℂ) ^ order.val * x i) =
      (∑ i, weights i * (Real.log (nodes i : ℝ) : ℂ) ^ order.val * y i) at ho
    calc
      _ = (∑ i, weights i * (Real.log (nodes i : ℝ) : ℂ) ^ order.val * x i) -
          (∑ i, weights i * (Real.log (nodes i : ℝ) : ℂ) ^ order.val * y i) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := sub_eq_zero.mpr ho
  funext i
  have hi := congrFun hz i
  have := (mul_eq_zero.mp hi).resolve_left (hweights i)
  exact sub_eq_zero.mp this

/-- Three literal nodes of a centered material bracket. -/
def centerLegMaterialNodes (c radius : ℕ) : Fin 3 → ℕ :=
  ![c - radius, c, c + radius]

def centerLegBracketWeights : Fin 3 → ℂ := ![1, -2, 1]

/-- Orders 0,1,2 of the actual centered bracket under the material log clock. -/
def centerLegClockJet (c radius : ℕ) :=
  materialBracketClockJet (centerLegMaterialNodes c radius) centerLegBracketWeights

/-- Three material-clock bracket readouts recover all three samples. -/
theorem centerLegClockJet_injective (c radius : ℕ)
    (hr : 0 < radius) (hc : radius < c) : Function.Injective (centerLegClockJet c radius) := by
  apply materialBracketClockJet_injective
  · intro i; fin_cases i <;> simp [centerLegMaterialNodes] <;> omega
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [centerLegMaterialNodes] at hij ⊢ <;> omega
  · intro i; fin_cases i <;> norm_num [centerLegBracketWeights]

/-- The order-zero row is the original second difference, with its -2 center. -/
theorem centerLegClockJet_zero (c radius : ℕ) (f : Fin 3 → ℂ) :
    centerLegClockJet c radius f 0 = f 0 - 2 * f 1 + f 2 := by
  simp [centerLegClockJet, materialBracketClockJet, centerLegBracketWeights,
    Fin.sum_univ_succ]
  ring

/-- Native Cp provenance: specializing the samples recovers its existing bracket. -/
theorem centerLegClockJet_nativeBracket (p radius k : ℕ) (s : ℂ)
    (hc : radius ≤ p * (k + 1)) :
    centerLegClockJet (p * (k + 1)) radius
      (fun i => realDirichletPower s (centerLegMaterialNodes (p * (k + 1)) radius i)) 0 =
      realCpPairBracket p radius k s := by
  rw [centerLegClockJet_zero]
  simp only [centerLegMaterialNodes, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, realCpPairBracket, Nat.cast_sub hc, Nat.cast_add, Nat.cast_mul]
  simp only [two_smul, Nat.cast_one]
  ring

/-- A sample invisible to order zero; no moment values enter its definition. -/
def centerLegInvisibleSample : Fin 3 → ℂ := ![1, 0, -1]

theorem centerLegInvisibleSample_bracket (c radius : ℕ) :
    centerLegClockJet c radius centerLegInvisibleSample 0 = 0 := by
  simp [centerLegClockJet_zero, centerLegInvisibleSample]

/-- The same sample becomes visible after one material log-clock application. -/
theorem centerLegInvisibleSample_clock (c radius : ℕ) :
    centerLegClockJet c radius centerLegInvisibleSample 1 =
      (Real.log ((c - radius : ℕ) : ℝ) : ℂ) -
        (Real.log ((c + radius : ℕ) : ℝ) : ℂ) := by
  simp only [centerLegClockJet, materialBracketClockJet, LinearMap.coe_mk, AddHom.coe_mk,
    Fin.sum_univ_three, centerLegBracketWeights, centerLegMaterialNodes,
    centerLegInvisibleSample, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_one, pow_one]
  ring

/-- Exact ratio orientation: lower material endpoint divided by upper endpoint. -/
theorem centerLegInvisibleSample_clock_eq_logRatio (c radius : ℕ)
    (hr : 0 < radius) (hc : radius < c) :
    centerLegClockJet c radius centerLegInvisibleSample 1 =
      (Real.log (((c - radius : ℕ) : ℝ) / ((c + radius : ℕ) : ℝ)) : ℂ) := by
  have hl : ((c - radius : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show c - radius ≠ 0 by omega)
  have hu : ((c + radius : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show c + radius ≠ 0 by omega)
  rw [centerLegInvisibleSample_clock, Real.log_div hl hu, Complex.ofReal_sub]

theorem centerLegInvisibleSample_clock_ne_zero (c radius : ℕ)
    (hr : 0 < radius) (hc : radius < c) :
    centerLegClockJet c radius centerLegInvisibleSample 1 ≠ 0 := by
  rw [centerLegInvisibleSample_clock, sub_ne_zero]
  apply fun hij => (ne_of_lt (Real.log_lt_log
    (show 0 < ((c - radius : ℕ) : ℝ) by exact_mod_cast (show 0 < c - radius by omega))
    (show ((c - radius : ℕ) : ℝ) < ((c + radius : ℕ) : ℝ) by
      exact_mod_cast (show c - radius < c + radius by omega))))
    (Complex.ofReal_injective hij)

/-- The saturated camera block has consecutive material nodes, centered at h.
The condition c>h will certify that all of them are positive. -/
def cameraBlockMaterialNodes (c h : ℕ) (i : Fin (2 * h + 1)) : ℕ := c - h + i.val

/-- Sum of radius-1,...,h brackets: each leg has weight 1; the center has -2h. -/
def cameraBlockBracketWeights (h : ℕ) (i : Fin (2 * h + 1)) : ℂ :=
  if i.val = h then -(2 * (h : ℂ)) else 1

def cameraBlockClockJet (c h : ℕ) :=
  materialBracketClockJet (cameraBlockMaterialNodes c h) (cameraBlockBracketWeights h)

/-- Exact zero-clock energy-independent synthesis of all legs and the center. -/
theorem cameraBlockClockJet_zero (c h : ℕ) (f : Fin (2 * h + 1) → ℂ) :
    cameraBlockClockJet c h f 0 =
      (∑ i, f i) - (2 * (h : ℂ) + 1) * f ⟨h, by omega⟩ := by
  change (∑ i, cameraBlockBracketWeights h i *
    (Real.log (cameraBlockMaterialNodes c h i : ℝ) : ℂ) ^ (0 : Fin (2*h+1)).val * f i) = _
  simp only [Fin.val_zero, pow_zero, mul_one]
  have hw (i : Fin (2 * h + 1)) : cameraBlockBracketWeights h i * f i =
      f i - (if i = ⟨h, by omega⟩ then (2 * (h : ℂ) + 1) * f i else 0) := by
    by_cases hi : i = ⟨h, by omega⟩
    · subst i; simp [cameraBlockBracketWeights]; ring
    · have hv : i.val ≠ h := by intro he; apply hi; exact Fin.ext he
      simp [cameraBlockBracketWeights, hi, hv]
  simp_rw [hw]
  rw [Finset.sum_sub_distrib]
  simp

/-- The geometric weights are exactly the sum of all h centered brackets.
Both legs and the common center are synthesized before the scalar readout. -/
theorem cameraBlockClockJet_zero_eq_radiusBrackets (c h : ℕ)
    (f : Fin (2 * h + 1) → ℂ) :
    cameraBlockClockJet c h f 0 =
      ∑ r : Fin h, (f ⟨h - (r.val + 1), by omega⟩ -
        2 * f ⟨h, by omega⟩ + f ⟨h + (r.val + 1), by omega⟩) := by
  let g : Fin (h + (h + 1)) → ℂ := fun i => f ⟨i.val, by have := i.isLt; omega⟩
  have hs : (∑ i, f i) = ∑ i, g i := by
    simpa [g] using (Equiv.sum_comp (finCongr (show 2*h+1 = h+(h+1) by omega)) g)
  have hs' : (∑ i, f i) =
      (∑ r : Fin h, f ⟨r.val, by omega⟩) + f ⟨h, by omega⟩ +
        (∑ r : Fin h, f ⟨h + (r.val + 1), by omega⟩) := by
    rw [hs, Fin.sum_univ_add,
      Fin.sum_univ_succ (fun i : Fin (h+1) => g (Fin.natAdd h i))]
    dsimp [g]
    ring
  have hr : (∑ r : Fin h, f ⟨r.val, by omega⟩) =
      ∑ r : Fin h, f ⟨h - (r.val + 1), by omega⟩ := by
    calc
      _ = ∑ r : Fin h, f ⟨(Fin.rev r).val, by have := (Fin.rev r).isLt; omega⟩ :=
        (Equiv.sum_comp Fin.revPerm (fun r : Fin h => f ⟨r.val, by omega⟩)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro r _
        congr 1
  rw [cameraBlockClockJet_zero, hs', hr, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- All-radius native camera provenance at its literal center p(k+1). -/
theorem cameraBlockClockJet_nativeRadiusSum (p h k : ℕ) (s : ℂ)
    (hc : h < p * (k + 1)) :
    cameraBlockClockJet (p * (k + 1)) h
      (fun i => realDirichletPower s (cameraBlockMaterialNodes (p * (k + 1)) h i)) 0 =
      ∑ r : Fin h, realCpPairBracket p (r.val + 1) k s := by
  rw [cameraBlockClockJet_zero_eq_radiusBrackets]
  apply Finset.sum_congr rfl
  intro r _
  have hl : p * (k+1) - h + (h - (r.val+1)) = p * (k+1) - (r.val+1) := by omega
  have hm : p * (k+1) - h + h = p * (k+1) := by omega
  have hu : p * (k+1) - h + (h + (r.val+1)) = p * (k+1) + (r.val+1) := by omega
  have hb : r.val+1 ≤ p * (k+1) := by omega
  simp only [cameraBlockMaterialNodes, hl, hm, hu, realCpPairBracket,
    Nat.cast_sub hb, Nat.cast_add, Nat.cast_mul, Nat.cast_one, two_smul]
  ring

/-- A block of 2h+1 nodes is recovered by clock orders 0,...,2h.
This local count is not a global density or a height-moment statement. -/
theorem cameraBlockClockJet_injective (c h : ℕ) (hh : 0 < h) (hc : h < c) :
    Function.Injective (cameraBlockClockJet c h) := by
  apply materialBracketClockJet_injective
  · intro i; dsimp [cameraBlockMaterialNodes]; omega
  · intro i j hij
    apply Fin.ext
    dsimp [cameraBlockMaterialNodes] at hij
    omega
  · intro i
    dsimp [cameraBlockBracketWeights]
    split_ifs
    · have hn : (h : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hh)
      exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) hn)
    · norm_num

end
end CarrySelfAdjointOperator
