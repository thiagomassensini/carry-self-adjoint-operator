import CarrySelfAdjointOperator.NativeThetaScoreTransport

/-! The actual positive theta modes and their logarithmic slopes.  The full
source score is a weighted average of these slopes; the remaining modes are
retained as an explicit nonnegative summable density. -/
namespace CarrySelfAdjointOperator
open Set Filter MeasureTheory XiThetaScore
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

def nativeThetaModeParameter (n : ℕ) (u : ℝ) : ℝ :=
  Real.pi*((n+1 : ℕ) : ℝ)^2*Real.exp (2*u)

def nativeThetaModeWeight (n : ℕ) (u : ℝ) : ℝ :=
  8*Real.pi^2*atom 4 (9/2) n u - 12*Real.pi*atom 2 (5/2) n u

def nativeThetaModeFirst (n : ℕ) (u : ℝ) : ℝ :=
  8*Real.pi^2*((9/2)*atom 4 (9/2) n u - 2*Real.pi*atom 6 (13/2) n u) -
    12*Real.pi*((5/2)*atom 2 (5/2) n u - 2*Real.pi*atom 4 (9/2) n u)

def nativeThetaModeSlope (p : ℝ) : ℝ := 2*p-9/2-6/(2*p-3)

def nativeThetaModeScore (n : ℕ) (u : ℝ) : ℝ :=
  u*nativeThetaModeSlope (nativeThetaModeParameter n u)

theorem nativeThetaModeWeight_eq (n : ℕ) (u : ℝ) :
    nativeThetaModeWeight n u = 2*completedNativeXiCosineKernelTerm (n+1 : ℤ) u := by
  rw [completedNativeXiCosineKernelTerm_eq]
  simp only [nativeThetaModeWeight, atom, Int.cast_add, Int.cast_natCast,
    Int.cast_one, Nat.cast_add, Nat.cast_one]
  ring_nf

theorem nativeThetaModeWeight_pos (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 < nativeThetaModeWeight n u := by
  rw [nativeThetaModeWeight_eq]
  exact mul_pos (by norm_num) (completedNativeXiCosineKernelTerm_pos (by omega) hu)

theorem nativeThetaModeWeight_hasDerivAt (n : ℕ) (u : ℝ) :
    HasDerivAt (nativeThetaModeWeight n) (nativeThetaModeFirst n u) u := by
  have h := ((atom_hasDerivAt 4 (9/2) n u).const_mul (8*Real.pi^2)).sub
    ((atom_hasDerivAt 2 (5/2) n u).const_mul (12*Real.pi))
  apply h.congr_deriv
  norm_num [nativeThetaModeFirst]

private theorem atom_factored (k : ℕ) (n : ℕ) (u : ℝ) :
    atom (2*k) ((1/2 : ℝ)+2*k) n u =
      ((n+1 : ℕ) : ℝ)^(2*k)*Real.exp (2*u)^k*Real.exp (u/2)*
        Real.exp (-nativeThetaModeParameter n u) := by
  unfold atom nativeThetaModeParameter
  rw [show ((1/2 : ℝ)+2*k)*u = (2*u)*(k : ℝ)+u/2 by ring,
    Real.exp_add, mul_comm (2*u) (k : ℝ), Real.exp_nat_mul]
  ring

theorem nativeThetaModeScore_mul_weight (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    nativeThetaModeScore n u*nativeThetaModeWeight n u = -u*nativeThetaModeFirst n u := by
  have hp : 3 < nativeThetaModeParameter n u := by
    have hm : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have he : 1 ≤ Real.exp (2*u) := Real.one_le_exp (by linarith)
    unfold nativeThetaModeParameter
    have hm2 : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ)^2 := by nlinarith
    nlinarith [Real.pi_gt_three, mul_le_mul hm2 he (by positivity) (sq_nonneg (((n+1 : ℕ) : ℝ)))]
  have h2 := atom_factored 1 n u
  have h4 := atom_factored 2 n u
  have h6 := atom_factored 3 n u
  norm_num at h2 h4 h6
  unfold nativeThetaModeScore nativeThetaModeSlope nativeThetaModeWeight nativeThetaModeFirst
  rw [h2,h4,h6]
  have hd : 2*nativeThetaModeParameter n u-3 ≠ 0 := by linarith
  field_simp [hd]
  unfold nativeThetaModeParameter
  push_cast
  ring

theorem nativeThetaModeSlope_mono {p q : ℝ} (hp : 3 ≤ p) (hpq : p ≤ q) :
    nativeThetaModeSlope p ≤ nativeThetaModeSlope q := by
  have hd : 6/(2*q-3) ≤ 6/(2*p-3) := by
    apply (div_le_div_iff₀ (by linarith : 0 < 2*q-3) (by linarith : 0 < 2*p-3)).2
    nlinarith
  unfold nativeThetaModeSlope
  linarith

theorem nativeThetaModeSlope_difference_le {p q : ℝ} (hp : 3 ≤ p) (hpq : p ≤ q) :
    nativeThetaModeSlope q-nativeThetaModeSlope p ≤ 2*q := by
  have h₁ : 6/(2*p-3) ≤ 2 := (div_le_iff₀ (by linarith : 0 < 2*p-3)).2 (by linarith)
  have h₂ : 0 ≤ 6/(2*q-3) := div_nonneg (by norm_num) (by linarith)
  unfold nativeThetaModeSlope
  linarith

theorem nativeThetaModeParameter_first_le (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    3 ≤ nativeThetaModeParameter 0 u ∧
      nativeThetaModeParameter 0 u ≤ nativeThetaModeParameter n u := by
  have he : 1 ≤ Real.exp (2*u) := Real.one_le_exp (by linarith)
  have hm : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hm2 : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ)^2 := by nlinarith
  simp only [nativeThetaModeParameter, zero_add, Nat.cast_one, one_pow, mul_one]
  constructor
  · nlinarith [Real.pi_gt_three]
  · nlinarith [mul_nonneg (Real.pi_pos.le) (Real.exp_pos (2*u)).le,
      mul_nonneg (Real.pi_pos.le) (sub_nonneg.mpr hm2)]

theorem nativeThetaModeScore_first_le (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    nativeThetaModeScore 0 u ≤ nativeThetaModeScore n u := by
  obtain ⟨hp,hpq⟩ := nativeThetaModeParameter_first_le n hu
  exact mul_le_mul_of_nonneg_left (nativeThetaModeSlope_mono hp hpq) hu

theorem nativeThetaModeWeight_summable (u : ℝ) :
    Summable (fun n => nativeThetaModeWeight n u) :=
  ((atom_summable 4 (9/2) u).mul_left (8*Real.pi^2)).sub
    ((atom_summable 2 (5/2) u).mul_left (12*Real.pi))

theorem nativeThetaModeFirst_summable (u : ℝ) :
    Summable (fun n => nativeThetaModeFirst n u) :=
  (((atom_summable 4 (9/2) u).mul_left (9/2)).sub
    ((atom_summable 6 (13/2) u).mul_left (2*Real.pi))).mul_left (8*Real.pi^2) |>.sub
      ((((atom_summable 2 (5/2) u).mul_left (5/2)).sub
        ((atom_summable 4 (9/2) u).mul_left (2*Real.pi))).mul_left (12*Real.pi))

theorem nativeThetaModeWeight_tsum (u : ℝ) :
    ∑' n : ℕ, nativeThetaModeWeight n u = completedNativeXiCosineKernel u := by
  simp only [nativeThetaModeWeight_eq, tsum_mul_left]
  exact (completedNativeXiCosineKernel_eq_two_mul_tsum u).symm

theorem nativeThetaModeFirst_tsum (u : ℝ) :
    ∑' n : ℕ, nativeThetaModeFirst n u = completedNativeXiCosineKernelFirst u := by
  unfold nativeThetaModeFirst completedNativeXiCosineKernelFirst
  rw [((((atom_summable 4 (9/2) u).mul_left (9/2)).sub
    ((atom_summable 6 (13/2) u).mul_left (2*Real.pi))).mul_left (8*Real.pi^2)).tsum_sub
      ((((atom_summable 2 (5/2) u).mul_left (5/2)).sub
        ((atom_summable 4 (9/2) u).mul_left (2*Real.pi))).mul_left (12*Real.pi))]
  simp only [tsum_mul_left]
  rw [((atom_summable 4 (9/2) u).mul_left (9/2)).tsum_sub
    ((atom_summable 6 (13/2) u).mul_left (2*Real.pi)),
    ((atom_summable 2 (5/2) u).mul_left (5/2)).tsum_sub
      ((atom_summable 4 (9/2) u).mul_left (2*Real.pi))]
  simp only [tsum_mul_left, atomSum]

/-- The full tail of the first-mode score approximation, still multiplied by
its own source weight.  It is not identified with a physical transport defect. -/
def nativeThetaScoreRemainderDensity (u : ℝ) : ℝ :=
  ∑' n : ℕ, (nativeThetaModeScore n u-nativeThetaModeScore 0 u)*nativeThetaModeWeight n u

theorem nativeThetaScoreRemainderDensity_summable {u : ℝ} (hu : 0 ≤ u) :
    Summable (fun n => (nativeThetaModeScore n u-nativeThetaModeScore 0 u)*nativeThetaModeWeight n u) := by
  have h := ((nativeThetaModeFirst_summable u).mul_left (-u)).sub
    ((nativeThetaModeWeight_summable u).mul_left (nativeThetaModeScore 0 u))
  apply h.congr
  intro n
  rw [← nativeThetaModeScore_mul_weight n hu]
  ring

theorem nativeThetaScoreRemainderDensity_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ nativeThetaScoreRemainderDensity u := by
  apply tsum_nonneg
  intro n
  exact mul_nonneg (sub_nonneg.mpr (nativeThetaModeScore_first_le n hu))
    (nativeThetaModeWeight_pos n hu).le

theorem nativeThetaScoreRemainderDensity_eq {u : ℝ} (hu : 0 ≤ u) :
    nativeThetaScoreRemainderDensity u =
      (nativeThetaScore u-nativeThetaModeScore 0 u)*completedNativeXiCosineKernel u := by
  have he : (fun n => (nativeThetaModeScore n u-nativeThetaModeScore 0 u)*nativeThetaModeWeight n u) =
      fun n => (-u)*nativeThetaModeFirst n u-nativeThetaModeScore 0 u*nativeThetaModeWeight n u := by
    funext n
    rw [← nativeThetaModeScore_mul_weight n hu]
    ring
  unfold nativeThetaScoreRemainderDensity
  rw [he, ((nativeThetaModeFirst_summable u).mul_left (-u)).tsum_sub
    ((nativeThetaModeWeight_summable u).mul_left (nativeThetaModeScore 0 u)),
    tsum_mul_left, tsum_mul_left, nativeThetaModeFirst_tsum, nativeThetaModeWeight_tsum]
  unfold nativeThetaScore
  field_simp [(completedNativeXiCosineKernel_pos hu).ne']

theorem nativeThetaScore_firstMode_lower_bound {u : ℝ} (hu : 0 ≤ u) :
    nativeThetaModeScore 0 u ≤ nativeThetaScore u := by
  have h := nativeThetaScoreRemainderDensity_nonneg hu
  rw [nativeThetaScoreRemainderDensity_eq hu] at h
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right (completedNativeXiCosineKernel_pos hu)).mp h)

end
end CarrySelfAdjointOperator
