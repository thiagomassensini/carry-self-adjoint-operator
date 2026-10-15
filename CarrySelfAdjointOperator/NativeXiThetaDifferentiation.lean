import CarrySelfAdjointOperator.NativeSourceThetaGreenTransport

/-! Differentiation of the ORIGINAL completed theta kernel.  The atom bounds
justify the infinite derivative and polynomially weighted integration by parts;
no finite-mode kernel replaces the source. -/
namespace CarrySelfAdjointOperator
open Set Filter MeasureTheory
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace XiThetaScore

def atom (k : ℕ) (a : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  ((n+1 : ℕ) : ℝ)^k * Real.exp (a*u) *
    Real.exp (-Real.pi * ((n+1 : ℕ) : ℝ)^2 * Real.exp (2*u))

theorem atom_nonneg (k : ℕ) (a : ℝ) (n : ℕ) (u : ℝ) : 0 ≤ atom k a n u := by
  unfold atom; positivity

theorem atom_summable (k : ℕ) (a u : ℝ) : Summable (fun n => atom k a n u) := by
  have h := (HurwitzKernelBounds.summable_f_nat k 1 (Real.exp_pos (2*u))).mul_left
    (Real.exp (a*u))
  simpa only [HurwitzKernelBounds.f_nat, atom, Nat.cast_add, Nat.cast_one,
    mul_assoc, mul_left_comm, mul_comm] using h

theorem atom_hasDerivAt (k : ℕ) (a : ℝ) (n : ℕ) (u : ℝ) :
    HasDerivAt (atom k a n)
      (a*atom k a n u - 2*Real.pi*atom (k+2) (a+2) n u) u := by
  have h₁ := ((hasDerivAt_id u).const_mul a).exp
  have h₂ := ((((hasDerivAt_id u).const_mul 2).exp).const_mul
    (-Real.pi * ((n+1 : ℕ) : ℝ)^2)).exp
  have h := (h₁.mul h₂).const_mul (((n+1 : ℕ) : ℝ)^k)
  apply (h.congr_of_eventuallyEq (Eventually.of_forall (fun v => by
    simp only [atom, Pi.mul_apply, id_eq]; ring))).congr_deriv
  simp only [atom, pow_add, id_eq]
  rw [show (a+2)*u = a*u+2*u by ring, Real.exp_add]
  ring

private def localBound (k : ℕ) (a x : ℝ) (n : ℕ) : ℝ :=
  ((n+1 : ℕ) : ℝ)^k * Real.exp (a*(x+1)) *
    Real.exp (-Real.pi * ((n+1 : ℕ) : ℝ)^2 * Real.exp (2*(x-1)))

private theorem localBound_summable (k : ℕ) (a x : ℝ) :
    Summable (localBound k a x) := by
  have h := (atom_summable k 0 (x-1)).mul_left (Real.exp (a*(x+1)))
  have he : localBound k a x = fun n => Real.exp (a*(x+1))*atom k 0 n (x-1) := by
    funext n
    simp only [localBound, atom, zero_mul, Real.exp_zero, mul_one]
    ring
  rw [he]
  exact h

private theorem atom_le_localBound (k : ℕ) {a x u : ℝ} (ha : 0 ≤ a)
    (hu : u ∈ Ioo (x-1) (x+1)) (n : ℕ) : atom k a n u ≤ localBound k a x n := by
  have h₁ : Real.exp (a*u) ≤ Real.exp (a*(x+1)) := by
    apply Real.exp_le_exp.mpr; nlinarith [hu.2]
  have h₂ : Real.exp (-Real.pi * ((n+1 : ℕ) : ℝ)^2 * Real.exp (2*u)) ≤
      Real.exp (-Real.pi * ((n+1 : ℕ) : ℝ)^2 * Real.exp (2*(x-1))) := by
    apply Real.exp_le_exp.mpr
    have he : Real.exp (2*(x-1)) ≤ Real.exp (2*u) :=
      Real.exp_le_exp.mpr (by linarith [hu.1])
    nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg (((n+1 : ℕ) : ℝ)))]
  unfold atom localBound
  gcongr

def atomSum (k : ℕ) (a u : ℝ) : ℝ := ∑' n : ℕ, atom k a n u

theorem atomSum_hasDerivAt (k : ℕ) {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    HasDerivAt (atomSum k a)
      (a*atomSum k a x - 2*Real.pi*atomSum (k+2) (a+2) x) x := by
  let B := fun n => |a| *localBound k a x n +
    (2*Real.pi)*localBound (k+2) (a+2) x n
  have hB : Summable B := ((localBound_summable k a x).mul_left |a|).add
    ((localBound_summable (k+2) (a+2) x).mul_left (2*Real.pi))
  have hbound (n : ℕ) (u : ℝ) (hu : u ∈ Ioo (x-1) (x+1)) :
      ‖a*atom k a n u - 2*Real.pi*atom (k+2) (a+2) n u‖ ≤ B n := by
    rw [Real.norm_eq_abs]
    calc
      |_ - _| ≤ |a*atom k a n u| + |2*Real.pi*atom (k+2) (a+2) n u| := abs_sub _ _
      _ = |a| *atom k a n u + (2*Real.pi)*atom (k+2) (a+2) n u := by
        rw [abs_mul, abs_of_nonneg (atom_nonneg k a n u),
          abs_of_nonneg (mul_nonneg (by positivity) (atom_nonneg (k+2) (a+2) n u))]
      _ ≤ B n := add_le_add
        (mul_le_mul_of_nonneg_left (atom_le_localBound k ha hu n) (abs_nonneg a))
        (mul_le_mul_of_nonneg_left (atom_le_localBound (k+2) (by linarith : 0 ≤ a+2) hu n)
          (by positivity))
  have hx : x ∈ Ioo (x-1) (x+1) := by constructor <;> linarith
  have h := hasDerivAt_tsum_of_isPreconnected
    (g := atom k a) (g' := fun n u => a*atom k a n u - 2*Real.pi*atom (k+2) (a+2) n u)
    hB isOpen_Ioo isPreconnected_Ioo (fun n u _ => atom_hasDerivAt k a n u)
    hbound hx (atom_summable k a x) hx
  apply h.congr_deriv
  rw [((atom_summable k a x).mul_left a).tsum_sub
    ((atom_summable (k+2) (a+2) x).mul_left (2*Real.pi)), tsum_mul_left, tsum_mul_left]
  rfl

/-- A summable coefficient controlling ALL positive modes, not a truncation. -/
def decayCoefficient (k n : ℕ) : ℝ :=
  ((n+1 : ℕ) : ℝ)^k * Real.exp (-Real.pi * ((n+1 : ℕ) : ℝ)^2 / 2)

theorem decayCoefficient_summable (k : ℕ) : Summable (decayCoefficient k) := by
  have h := HurwitzKernelBounds.summable_f_nat k 1 (by norm_num : (0 : ℝ) < 1/2)
  convert h using 1
  funext n
  simp only [decayCoefficient, HurwitzKernelBounds.f_nat, Nat.cast_add, Nat.cast_one]
  congr 2
  ring

private theorem gaussian_decay {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    Real.exp (-Real.pi * ((n+1 : ℕ) : ℝ)^2 * Real.exp (2*u)) ≤
      Real.exp (-Real.pi * ((n+1 : ℕ) : ℝ)^2 / 2) * Real.exp (-8*u) := by
  let c := Real.pi * ((n+1 : ℕ) : ℝ)^2
  have hm : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hc : 3 ≤ c := by
    dsimp [c]
    have hm2 : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ)^2 := by nlinarith
    nlinarith [Real.pi_gt_three, mul_nonneg (Real.pi_pos.le) (sub_nonneg.mpr hm2)]
  have he : (1+u)^2 ≤ Real.exp (2*u) := by
    rw [show 2*u = u+u by ring, Real.exp_add]
    nlinarith [Real.add_one_le_exp u, Real.exp_pos u]
  have hq : (1/2 : ℝ)+2*u+u^2 ≤ Real.exp (2*u)-1/2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hq (by linarith : 0 ≤ c)
  have hbase : 8*u ≤ 3*((1/2 : ℝ)+2*u+u^2) := by nlinarith [sq_nonneg (u-1/3)]
  have hh := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (1/2 : ℝ)+2*u+u^2)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have heq : -Real.pi * ((n+1 : ℕ) : ℝ)^2 = -c := by dsimp [c]; ring
  rw [heq]
  nlinarith

theorem atom_decay (k : ℕ) {a u : ℝ} (ha : a ≤ 13/2) (hu : 0 ≤ u) (n : ℕ) :
    atom k a n u ≤ decayCoefficient k n * Real.exp (-(3/2 : ℝ)*u) := by
  unfold atom decayCoefficient
  calc
    _ ≤ ((n+1 : ℕ) : ℝ)^k * Real.exp (a*u) *
        (Real.exp (-Real.pi * ((n+1 : ℕ) : ℝ)^2 / 2) * Real.exp (-8*u)) := by
      gcongr; exact gaussian_decay hu n
    _ = ((n+1 : ℕ) : ℝ)^k * Real.exp (-Real.pi * ((n+1 : ℕ) : ℝ)^2 / 2) *
        Real.exp ((a-8)*u) := by
      rw [show (a-8)*u = a*u+(-8*u) by ring, Real.exp_add]
      ring
    _ ≤ _ := by gcongr; nlinarith

theorem atomSum_decay (k : ℕ) {a : ℝ} (ha : a ≤ 13/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : ℝ}, 0 ≤ u →
      ‖atomSum k a u‖ ≤ C*Real.exp (-(3/2 : ℝ)*u) := by
  refine ⟨∑' n : ℕ, decayCoefficient k n, tsum_nonneg (fun n => by unfold decayCoefficient; positivity), ?_⟩
  intro u hu
  unfold atomSum
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun n => atom_nonneg k a n u))]
  exact ((atom_summable k a u).tsum_le_tsum (atom_decay k ha hu)
    ((decayCoefficient_summable k).mul_right (Real.exp (-(3/2 : ℝ)*u)))).trans_eq
      tsum_mul_right

end XiThetaScore

open XiThetaScore

theorem completedNativeXiCosineKernel_eq_atomSum (u : ℝ) :
    completedNativeXiCosineKernel u =
      8*Real.pi^2*atomSum 4 (9/2) u - 12*Real.pi*atomSum 2 (5/2) u := by
  rw [completedNativeXiCosineKernel_eq_two_mul_tsum]
  have he : (fun n : ℕ => completedNativeXiCosineKernelTerm (n+1 : ℤ) u) =
      fun n => (4*Real.pi^2)*atom 4 (9/2) n u - (6*Real.pi)*atom 2 (5/2) n u := by
    funext n
    rw [completedNativeXiCosineKernelTerm_eq]
    simp only [atom, Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add, Nat.cast_one]
    ring_nf
  rw [he, ((atom_summable 4 (9/2) u).mul_left (4*Real.pi^2)).tsum_sub
    ((atom_summable 2 (5/2) u).mul_left (6*Real.pi)), tsum_mul_left, tsum_mul_left]
  unfold atomSum
  ring

/-- The derivative of the full source, justified by locally uniform mode bounds. -/
def completedNativeXiCosineKernelFirst (u : ℝ) : ℝ :=
  8*Real.pi^2*((9/2)*atomSum 4 (9/2) u - 2*Real.pi*atomSum 6 (13/2) u) -
    12*Real.pi*((5/2)*atomSum 2 (5/2) u - 2*Real.pi*atomSum 4 (9/2) u)

theorem completedNativeXiCosineKernel_hasDerivAt (u : ℝ) :
    HasDerivAt completedNativeXiCosineKernel (completedNativeXiCosineKernelFirst u) u := by
  have h := ((atomSum_hasDerivAt 4 (by norm_num : (0 : ℝ) ≤ 9/2) u).const_mul (8*Real.pi^2)).sub
    ((atomSum_hasDerivAt 2 (by norm_num : (0 : ℝ) ≤ 5/2) u).const_mul (12*Real.pi))
  apply (h.congr_of_eventuallyEq (Eventually.of_forall completedNativeXiCosineKernel_eq_atomSum)).congr_deriv
  norm_num [completedNativeXiCosineKernelFirst]

theorem completedNativeXiCosineKernelFirst_decay :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : ℝ}, 0 ≤ u →
      ‖completedNativeXiCosineKernelFirst u‖ ≤ C*Real.exp (-(3/2 : ℝ)*u) := by
  obtain ⟨C4,h4,b4⟩ := atomSum_decay 4 (by norm_num : (9/2 : ℝ) ≤ 13/2)
  obtain ⟨C6,h6,b6⟩ := atomSum_decay 6 (by norm_num : (13/2 : ℝ) ≤ 13/2)
  obtain ⟨C2,h2,b2⟩ := atomSum_decay 2 (by norm_num : (5/2 : ℝ) ≤ 13/2)
  refine ⟨8*Real.pi^2*((9/2)*C4+2*Real.pi*C6)+12*Real.pi*((5/2)*C2+2*Real.pi*C4), by positivity, ?_⟩
  intro u hu
  simp only [completedNativeXiCosineKernelFirst]
  calc
    ‖_ - _‖ ≤ ‖8*Real.pi^2*((9/2)*atomSum 4 (9/2) u - 2*Real.pi*atomSum 6 (13/2) u)‖ +
      ‖12*Real.pi*((5/2)*atomSum 2 (5/2) u - 2*Real.pi*atomSum 4 (9/2) u)‖ := norm_sub_le _ _
    _ ≤ 8*Real.pi^2*((9/2)*‖atomSum 4 (9/2) u‖+2*Real.pi*‖atomSum 6 (13/2) u‖)+
        12*Real.pi*((5/2)*‖atomSum 2 (5/2) u‖+2*Real.pi*‖atomSum 4 (9/2) u‖) := by
      have hb (a b A B : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
          ‖a*A-b*B‖ ≤ a*‖A‖+b*‖B‖ := by
        calc
          _ ≤ ‖a*A‖+‖b*B‖ := norm_sub_le _ _
          _ = _ := by rw [norm_mul, norm_mul, Real.norm_eq_abs a, Real.norm_eq_abs b,
            abs_of_nonneg ha, abs_of_nonneg hb]
      rw [norm_mul (8*Real.pi^2), norm_mul (12*Real.pi), Real.norm_eq_abs (8*Real.pi^2),
        Real.norm_eq_abs (12*Real.pi), abs_of_nonneg (by positivity : 0 ≤ 8*Real.pi^2),
        abs_of_nonneg (by positivity : 0 ≤ 12*Real.pi)]
      exact add_le_add (mul_le_mul_of_nonneg_left (hb _ _ _ _ (by norm_num) (by positivity)) (by positivity))
        (mul_le_mul_of_nonneg_left (hb _ _ _ _ (by norm_num) (by positivity)) (by positivity))
    _ ≤ _ := by
      calc
        _ ≤ 8*Real.pi^2*((9/2)*(C4*Real.exp (-(3/2 : ℝ)*u))+2*Real.pi*(C6*Real.exp (-(3/2 : ℝ)*u)))+
            12*Real.pi*((5/2)*(C2*Real.exp (-(3/2 : ℝ)*u))+2*Real.pi*(C4*Real.exp (-(3/2 : ℝ)*u))) := by
          gcongr <;> first | exact b4 hu | exact b6 hu | exact b2 hu
        _ = _ := by ring

end
end CarrySelfAdjointOperator
