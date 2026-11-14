import CarrySelfAdjointOperator.RadialVandermondeJetRecurrence
import CarrySelfAdjointOperator.CompletedNativeChiralEvenBoundaryEnergy
import CarrySelfAdjointOperator.CompletedNativeChiralReturnSevenMarginLoss
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# First radial correction in arbitrary dimension

The source response is kept as a finite truncation. No convergence assumption
on an arbitrary coefficient sequence is used in the algebraic coefficient
calculation.
-/

namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false

def radialVandermondeBoundaryBase {N : ℕ} (x : Fin N → ℂ) (m : ℕ) : ℂ :=
  if hm : m < N then x ⟨m,hm⟩ else 0

def radialVandermondeBoundarySlope {N : ℕ} (a : Fin N → ℝ)
    (x : Fin N → ℂ) (m : ℕ) : ℂ :=
  if hm : m = N then
    if hN : 0 < N then (∑ i : Fin N, a i : ℝ) * x ⟨N - 1, by omega⟩ else 0
  else 0

theorem radialVandermondeBoundaryCoordinate_zero {N : ℕ} (a : Fin N → ℝ)
    (x : Fin N → ℂ) (m : ℕ) :
    radialVandermondeBoundaryCoordinate a x 0 m = radialVandermondeBoundaryBase x m := by
  by_cases hm : m < N
  · simp [radialVandermondeBoundaryCoordinate, radialVandermondeBoundaryBase, hm]
  · simp [radialVandermondeBoundaryCoordinate, radialVandermondeBoundaryBase, hm,
      radialVandermondeHighCoordinate_factor a x 0 m (by omega)]

private theorem radialVandermondePowerTerm_hasDerivAt (c : ℝ) (z : ℂ)
    (k : ℕ) :
    HasDerivAt (fun t : ℝ => (((c * t^k : ℝ) : ℂ) * z))
      (((((k : ℝ) * 0^(k-1) * c : ℝ) : ℂ) * z)) 0 := by
  have h := ((((hasDerivAt_id (0 : ℝ)).pow k).mul_const c).ofReal_comp).mul_const z
  have hfun : (fun t : ℝ => (((c * t^k : ℝ) : ℂ) * z)) =
      (fun t : ℝ => (((t^k * c : ℝ) : ℂ) * z)) := by
    funext t
    congr 2
    ring
  rw [hfun]
  simpa only [Pi.pow_apply, id_eq, mul_one] using h

theorem radialVandermondeBoundaryCoordinate_hasDerivAt_zero {N : ℕ}
    (a : Fin N → ℝ) (x : Fin N → ℂ) (m : ℕ)
    (ha : Function.Injective a) (hN : 0 < N) :
    HasDerivAt (fun t : ℝ => radialVandermondeBoundaryCoordinate a x t m)
      (radialVandermondeBoundarySlope a x m) 0 := by
  classical
  by_cases hm : m < N
  · have hne : m ≠ N := by omega
    simpa [radialVandermondeBoundaryCoordinate, radialVandermondeBoundarySlope, hm, hne]
      using (hasDerivAt_const (0 : ℝ) (x ⟨m,hm⟩))
  · simp only [radialVandermondeBoundaryCoordinate, dif_neg hm]
    let c : Fin N → ℝ := fun j =>
      ∑ i : Fin N, a i ^ m * radialVandermondeInverse a i j
    have ht (j : Fin N) : HasDerivAt
        (fun t : ℝ => (((c j * t^(m-(j : ℕ)) : ℝ) : ℂ) * x j))
        (((((m-(j : ℕ) : ℕ) : ℝ) * 0^(m-(j : ℕ)-1) * c j : ℝ) : ℂ) * x j) 0 := by
      simpa only [c, Pi.pow_apply, id_eq, mul_one] using
        radialVandermondePowerTerm_hasDerivAt (c j) (x j) (m-(j : ℕ))
    have hs := HasDerivAt.fun_sum (fun j (_hj : j ∈ (Finset.univ : Finset (Fin N))) => ht j)
    have hfun : (fun t : ℝ => radialVandermondeHighCoordinate a x t m) =
        (fun t : ℝ => ∑ j : Fin N,
          (((c j * t^(m-(j : ℕ)) : ℝ) : ℂ) * x j)) := by
      funext t
      simp [radialVandermondeHighCoordinate, c, mul_comm]
    rw [hfun]
    by_cases heq : m = N
    · subst m
      have hsum : (∑ j : Fin N,
          (((((N-(j : ℕ) : ℕ) : ℝ) * 0^(N-(j : ℕ)-1) * c j : ℝ) : ℂ) * x j)) =
          (∑ i : Fin N, a i : ℝ) * x ⟨N - 1, by omega⟩ := by
        let last : Fin N := ⟨N-1, by omega⟩
        have hlast : c last = ∑ i : Fin N, a i := by
          exact radialVandermonde_lastHighMoment a ha hN
        rw [← Finset.add_sum_erase (a := last) _ _ (Finset.mem_univ last)]
        have hmain : (((((N-(last : ℕ) : ℕ) : ℝ) * 0^(N-(last : ℕ)-1) * c last : ℝ) : ℂ) * x last) =
            (∑ i : Fin N, a i : ℝ) * x last := by
          have hidx : N - (last : ℕ) = 1 := by change N - (N-1) = 1; omega
          simp [hidx, hlast]
        rw [hmain]
        have hrest : ∑ j ∈ Finset.univ.erase last,
            (((((N-(j : ℕ) : ℕ) : ℝ) * 0^(N-(j : ℕ)-1) * c j : ℝ) : ℂ) * x j) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          have hjlt : (j : ℕ) < N-1 := by
            have hjne : j ≠ last := Finset.ne_of_mem_erase hj
            have hjval : (j : ℕ) ≠ N-1 := by
              intro h
              apply hjne
              apply Fin.ext
              simpa [last] using h
            omega
          have hpow : N-(j : ℕ)-1 ≠ 0 := by omega
          simp [hpow]
        rw [hrest, add_zero]
      convert hs using 1
      · rfl
      · simpa [radialVandermondeBoundarySlope, hN] using hsum.symm
    · have hlt : N < m := by omega
      have hsum : (∑ j : Fin N,
          (((((m-(j : ℕ) : ℕ) : ℝ) * 0^(m-(j : ℕ)-1) * c j : ℝ) : ℂ) * x j)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hpow : m-(j : ℕ)-1 ≠ 0 := by omega
        simp [hpow]
      convert hs using 1
      · rfl
      · simpa [radialVandermondeBoundarySlope, heq] using hsum.symm

/-- Finite response prefix containing every term that can affect its value or
first derivative at the radial boundary. It makes no convergence claim. -/
def radialVandermondeResponsePrefix {N : ℕ} (a : Fin N → ℝ)
    (β : ℕ → ℝ) (x : Fin N → ℂ) (t : ℝ) : ℝ :=
  2 * ∑ j ∈ Finset.range N, (-1 : ℝ)^j * β j *
    (∑ b ∈ Finset.range (2*j+1), (-1 : ℝ)^b *
      (conj (radialVandermondeBoundaryCoordinate a x t b) *
        radialVandermondeBoundaryCoordinate a x t (2*j-b)).re)

def radialVandermondeResponseFace {N : ℕ} (β : ℕ → ℝ)
    (x : Fin N → ℂ) : ℝ :=
  2 * ∑ j ∈ Finset.range N, (-1 : ℝ)^j * β j *
    (∑ b ∈ Finset.range (2*j+1), (-1 : ℝ)^b *
      (conj (radialVandermondeBoundaryBase x b) *
        radialVandermondeBoundaryBase x (2*j-b)).re)

def radialVandermondeResponseFirstCoefficient {N : ℕ} (a : Fin N → ℝ)
    (β : ℕ → ℝ) (x : Fin N → ℂ) : ℝ :=
  2 * ∑ j ∈ Finset.range N, (-1 : ℝ)^j * β j *
    (∑ b ∈ Finset.range (2*j+1), (-1 : ℝ)^b *
      (conj (radialVandermondeBoundarySlope a x b) *
          radialVandermondeBoundaryBase x (2*j-b) +
        conj (radialVandermondeBoundaryBase x b) *
          radialVandermondeBoundarySlope a x (2*j-b)).re)

theorem radialVandermondeResponsePrefix_zero {N : ℕ}
    (a : Fin N → ℝ) (β : ℕ → ℝ) (x : Fin N → ℂ) :
    radialVandermondeResponsePrefix a β x 0 = radialVandermondeResponseFace β x := by
  simp_rw [radialVandermondeResponsePrefix, radialVandermondeResponseFace,
    radialVandermondeBoundaryCoordinate_zero]

theorem radialVandermondeResponseFace_eq_nativeSourceFiniteBoundaryEnergy
    {N : ℕ} (x : Fin N → ℂ) :
    radialVandermondeResponseFace nativeSourceOddBoundaryCoefficient x =
      nativeSourceFiniteBoundaryEnergy N x := by
  unfold radialVandermondeResponseFace nativeSourceFiniteBoundaryEnergy
  simp [radialVandermondeBoundaryBase]

theorem radialVandermondeResponsePrefix_zero_eq_nativeSourceFiniteBoundaryEnergy
    {N : ℕ} (a : Fin N → ℝ) (x : Fin N → ℂ) :
    radialVandermondeResponsePrefix a nativeSourceOddBoundaryCoefficient x 0 =
      nativeSourceFiniteBoundaryEnergy N x := by
  rw [radialVandermondeResponsePrefix_zero,
    radialVandermondeResponseFace_eq_nativeSourceFiniteBoundaryEnergy]

theorem radialVandermondeResponsePrefix_hasDerivAt_zero {N : ℕ}
    (a : Fin N → ℝ) (β : ℕ → ℝ) (x : Fin N → ℂ)
    (ha : Function.Injective a) (hN : 0 < N) :
    HasDerivAt (fun t : ℝ => radialVandermondeResponsePrefix a β x t)
      (radialVandermondeResponseFirstCoefficient a β x) 0 := by
  classical
  have hp (b d : ℕ) : HasDerivAt
      (fun t : ℝ => (conj (radialVandermondeBoundaryCoordinate a x t b) *
        radialVandermondeBoundaryCoordinate a x t d).re)
      ((conj (radialVandermondeBoundarySlope a x b) *
        radialVandermondeBoundaryBase x d +
        conj (radialVandermondeBoundaryBase x b) *
          radialVandermondeBoundarySlope a x d).re) 0 := by
    have hd₁ := radialVandermondeBoundaryCoordinate_hasDerivAt_zero a x b ha hN
    have hd₂ := radialVandermondeBoundaryCoordinate_hasDerivAt_zero a x d ha hN
    have hv₁ := radialVandermondeBoundaryCoordinate_zero a x b
    have hv₂ := radialVandermondeBoundaryCoordinate_zero a x d
    have hp₀ : HasDerivAt
        (fun t : ℝ => (conj (radialVandermondeBoundaryCoordinate a x t b) *
          radialVandermondeBoundaryCoordinate a x t d).re)
        ((conj (radialVandermondeBoundarySlope a x b) *
          radialVandermondeBoundaryCoordinate a x 0 d +
          conj (radialVandermondeBoundaryCoordinate a x 0 b) *
            radialVandermondeBoundarySlope a x d).re) 0 := by
      exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hd₁.star.mul hd₂)
    simpa only [radialVandermondeBoundaryCoordinate_zero] using hp₀
  have hj (j : ℕ) : HasDerivAt
      (fun t : ℝ => (-1 : ℝ)^j * β j *
        (∑ b ∈ Finset.range (2*j+1), (-1 : ℝ)^b *
          (conj (radialVandermondeBoundaryCoordinate a x t b) *
            radialVandermondeBoundaryCoordinate a x t (2*j-b)).re))
      ((-1 : ℝ)^j * β j *
        (∑ b ∈ Finset.range (2*j+1), (-1 : ℝ)^b *
          (conj (radialVandermondeBoundarySlope a x b) *
              radialVandermondeBoundaryBase x (2*j-b) +
            conj (radialVandermondeBoundaryBase x b) *
              radialVandermondeBoundarySlope a x (2*j-b)).re)) 0 := by
    simpa only [Finset.sum_apply] using
      (HasDerivAt.fun_sum (fun b (_hb : b ∈ Finset.range (2*j+1)) =>
        (hp b (2*j-b)).const_mul ((-1 : ℝ)^b))).const_mul ((-1 : ℝ)^j * β j)
  have hs := (HasDerivAt.fun_sum (fun j (_hj : j ∈ Finset.range N) => hj j)).const_mul 2
  simpa only [radialVandermondeResponsePrefix, radialVandermondeResponseFirstCoefficient,
    Finset.sum_apply] using hs

def radialVandermondeFirstCorrectionClosed {N : ℕ} (a : Fin N → ℝ)
    (β : ℕ → ℝ) (x : Fin N → ℂ) : ℝ :=
  4 * (∑ i : Fin N, a i) *
    ∑ j ∈ Finset.range N,
      if hj : N ≤ 2*j ∧ 2*j-N < N then
        (-1 : ℝ)^(j+N) * β j *
          (conj (x ⟨2*j-N,hj.2⟩) * x ⟨N-1, by omega⟩).re
      else 0

private theorem radialVandermondeRealCross_swap (u v : ℂ) :
    (conj u * v).re = (conj v * u).re := by
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem radialVandermondeAlternating_reflection {N : ℕ}
    (a : Fin N → ℝ) (x : Fin N → ℂ) (j : ℕ) :
    (∑ b ∈ Finset.range (2*j+1), (-1 : ℝ)^b *
      (conj (radialVandermondeBoundaryBase x b) *
        radialVandermondeBoundarySlope a x (2*j-b)).re) =
    (∑ b ∈ Finset.range (2*j+1), (-1 : ℝ)^b *
      (conj (radialVandermondeBoundarySlope a x b) *
        radialVandermondeBoundaryBase x (2*j-b)).re) := by
  classical
  let f : ℕ → ℝ := fun b => (-1 : ℝ)^b *
    (conj (radialVandermondeBoundaryBase x b) *
      radialVandermondeBoundarySlope a x (2*j-b)).re
  have hsign (b : ℕ) (hb : b < 2*j+1) : (-1 : ℝ)^(2*j-b) = (-1 : ℝ)^b := by
    have hb' : b ≤ 2*j := by omega
    have hprod : (-1 : ℝ)^(2*j-b) * (-1 : ℝ)^b = 1 := by
      rw [← pow_add, Nat.sub_add_cancel hb']
      exact Even.neg_one_pow ⟨j, by omega⟩
    have hsquare : (-1 : ℝ)^b * (-1 : ℝ)^b = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨b, by omega⟩
    calc
      (-1 : ℝ)^(2*j-b) = (-1 : ℝ)^(2*j-b) * 1 := by simp
      _ = (-1 : ℝ)^(2*j-b) * ((-1 : ℝ)^b * (-1 : ℝ)^b) := by rw [hsquare]
      _ = ((-1 : ℝ)^(2*j-b) * (-1 : ℝ)^b) * (-1 : ℝ)^b := by ring
      _ = (-1 : ℝ)^b := by rw [hprod]; simp
  have hr := Finset.sum_range_reflect f (2*j+1)
  calc
    _ = ∑ b ∈ Finset.range (2*j+1), f b := by rfl
    _ = ∑ b ∈ Finset.range (2*j+1), f (2*j-b) := by simpa [f] using hr.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      have hb' : b ≤ 2*j := by simp only [Finset.mem_range] at hb; omega
      have hidx : 2*j-(2*j-b) = b := by omega
      change (-1 : ℝ)^(2*j-b) *
          (conj (radialVandermondeBoundaryBase x (2*j-b)) *
            radialVandermondeBoundarySlope a x (2*j-(2*j-b))).re = _
      rw [hidx, hsign b (by simp only [Finset.mem_range] at hb; omega)]
      exact congrArg (fun r : ℝ => (-1 : ℝ)^b * r)
        (radialVandermondeRealCross_swap
          (radialVandermondeBoundaryBase x (2*j-b))
          (radialVandermondeBoundarySlope a x b))

private theorem radialVandermondeSlopeBase_left_sum {N : ℕ}
    (a : Fin N → ℝ) (x : Fin N → ℂ) (j : ℕ) (hN : 0 < N) :
    (∑ b ∈ Finset.range (2*j+1), (-1 : ℝ)^b *
      (conj (radialVandermondeBoundarySlope a x b) *
        radialVandermondeBoundaryBase x (2*j-b)).re) =
      if hj : N ≤ 2*j ∧ 2*j-N < N then
        (-1 : ℝ)^N * (∑ i : Fin N, a i) *
          (conj (x ⟨2*j-N,hj.2⟩) * x ⟨N-1, by omega⟩).re
      else 0 := by
  classical
  by_cases hNj : N ≤ 2*j
  · by_cases hlow : 2*j-N < N
    · rw [dif_pos ⟨hNj,hlow⟩]
      have hmain : (-1 : ℝ)^N *
          (conj (radialVandermondeBoundarySlope a x N) *
            radialVandermondeBoundaryBase x (2*j-N)).re =
          (-1 : ℝ)^N * (∑ i : Fin N, a i) *
            (conj (x ⟨2*j-N,hlow⟩) * x ⟨N-1, by omega⟩).re := by
        have hslope : radialVandermondeBoundarySlope a x N =
            (∑ i : Fin N, a i : ℝ) * x ⟨N-1, by omega⟩ := by
          simp [radialVandermondeBoundarySlope, hN]
        have hbase : radialVandermondeBoundaryBase x (2*j-N) =
            x ⟨2*j-N,hlow⟩ := by
          simp [radialVandermondeBoundaryBase, hlow]
        have hre : (conj (((∑ i : Fin N, a i : ℝ) : ℂ) *
            x ⟨N-1, by omega⟩) * x ⟨2*j-N,hlow⟩).re =
            (∑ i : Fin N, a i : ℝ) *
              (conj (x ⟨N-1, by omega⟩) * x ⟨2*j-N,hlow⟩).re := by
          simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
          ring
        rw [hslope, hbase, hre,
          radialVandermondeRealCross_swap (x ⟨N-1, by omega⟩) (x ⟨2*j-N,hlow⟩)]
        ring
      rw [Finset.sum_eq_single N]
      · exact hmain
      · intro b hb hbn
        simp [radialVandermondeBoundarySlope, hbn]
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
    · rw [dif_neg (by simp [hNj, hlow])]
      apply Finset.sum_eq_zero
      intro b hb
      by_cases hbn : b = N
      · subst b
        simp [radialVandermondeBoundarySlope, radialVandermondeBoundaryBase, hN, hlow]
      · simp [radialVandermondeBoundarySlope, hbn]
  · rw [dif_neg (by simp [hNj])]
    apply Finset.sum_eq_zero
    intro b hb
    have hbN : b ≠ N := by
      intro h
      subst b
      have hb' : N ≤ 2*j := by simp only [Finset.mem_range] at hb; omega
      exact hNj hb'
    simp [radialVandermondeBoundarySlope, hbN]

theorem radialVandermondeResponseFirstCoefficient_eq_closed {N : ℕ}
    (a : Fin N → ℝ) (β : ℕ → ℝ) (x : Fin N → ℂ)
    (hN : 0 < N) :
    radialVandermondeResponseFirstCoefficient a β x =
      radialVandermondeFirstCorrectionClosed a β x := by
  classical
  unfold radialVandermondeResponseFirstCoefficient radialVandermondeFirstCorrectionClosed
  have hinner (j : ℕ) :
      (∑ b ∈ Finset.range (2*j+1), (-1 : ℝ)^b *
        (conj (radialVandermondeBoundarySlope a x b) *
            radialVandermondeBoundaryBase x (2*j-b) +
          conj (radialVandermondeBoundaryBase x b) *
            radialVandermondeBoundarySlope a x (2*j-b)).re) =
        2 * (if hj : N ≤ 2*j ∧ 2*j-N < N then
          (-1 : ℝ)^N * (∑ i : Fin N, a i) *
            (conj (x ⟨2*j-N,hj.2⟩) * x ⟨N-1, by omega⟩).re else 0) := by
    calc
      _ = (∑ b ∈ Finset.range (2*j+1), (-1 : ℝ)^b *
            (conj (radialVandermondeBoundarySlope a x b) *
              radialVandermondeBoundaryBase x (2*j-b)).re) +
          ∑ b ∈ Finset.range (2*j+1), (-1 : ℝ)^b *
            (conj (radialVandermondeBoundaryBase x b) *
              radialVandermondeBoundarySlope a x (2*j-b)).re := by
        simp_rw [Complex.add_re, mul_add]
        rw [Finset.sum_add_distrib]
      _ = 2 * (∑ b ∈ Finset.range (2*j+1), (-1 : ℝ)^b *
            (conj (radialVandermondeBoundarySlope a x b) *
              radialVandermondeBoundaryBase x (2*j-b)).re) := by
        rw [radialVandermondeAlternating_reflection a x j]
        ring
      _ = _ := by rw [radialVandermondeSlopeBase_left_sum a x j hN]
  have hterm (j : ℕ) :
      2 * ((-1 : ℝ)^j * β j *
        (2 * if hj : N ≤ 2*j ∧ 2*j-N < N then
          (-1 : ℝ)^N * (∑ i : Fin N, a i) *
            (conj (x ⟨2*j-N,hj.2⟩) * x ⟨N-1, by omega⟩).re else 0)) =
      (4 * (∑ i : Fin N, a i)) *
        (if hj : N ≤ 2*j ∧ 2*j-N < N then
          (-1 : ℝ)^(j+N) * β j *
            (conj (x ⟨2*j-N,hj.2⟩) * x ⟨N-1, by omega⟩).re else 0) := by
    by_cases hjvalid : N ≤ 2*j ∧ 2*j-N < N
    ·
      rw [dif_pos hjvalid, dif_pos hjvalid]
      have hsign : (-1 : ℝ)^j * (-1 : ℝ)^N = (-1 : ℝ)^(j+N) := by
        rw [← pow_add]
      calc
        _ = (4 * (∑ i : Fin N, a i)) *
            (((-1 : ℝ)^j * (-1 : ℝ)^N) * β j *
              (conj (x ⟨2*j-N,hjvalid.2⟩) * x ⟨N-1, by omega⟩).re) := by ring
        _ = (4 * (∑ i : Fin N, a i)) *
            ((-1 : ℝ)^(j+N) * β j *
              (conj (x ⟨2*j-N,hjvalid.2⟩) * x ⟨N-1, by omega⟩).re) := by rw [hsign]
    ·
      rw [dif_neg hjvalid, dif_neg hjvalid]
      simp
  calc
    2 * ∑ j ∈ Finset.range N, (-1 : ℝ)^j * β j *
        (∑ b ∈ Finset.range (2*j+1), (-1 : ℝ)^b *
          (conj (radialVandermondeBoundarySlope a x b) *
              radialVandermondeBoundaryBase x (2*j-b) +
            conj (radialVandermondeBoundaryBase x b) *
              radialVandermondeBoundarySlope a x (2*j-b)).re)
      = ∑ j ∈ Finset.range N, 2 * ((-1 : ℝ)^j * β j *
          (2 * if hj : N ≤ 2*j ∧ 2*j-N < N then
            (-1 : ℝ)^N * (∑ i : Fin N, a i) *
              (conj (x ⟨2*j-N,hj.2⟩) * x ⟨N-1, by omega⟩).re else 0)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hinner j]
    _ = ∑ j ∈ Finset.range N, (4 * (∑ i : Fin N, a i)) *
          (if hj : N ≤ 2*j ∧ 2*j-N < N then
            (-1 : ℝ)^(j+N) * β j *
              (conj (x ⟨2*j-N,hj.2⟩) * x ⟨N-1, by omega⟩).re else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hterm j
    _ = 4 * (∑ i : Fin N, a i) *
          ∑ j ∈ Finset.range N,
            if hj : N ≤ 2*j ∧ 2*j-N < N then
              (-1 : ℝ)^(j+N) * β j *
                (conj (x ⟨2*j-N,hj.2⟩) * x ⟨N-1, by omega⟩).re
            else 0 := by
        exact (Finset.mul_sum (Finset.range N)
          (fun j => if hj : N ≤ 2*j ∧ 2*j-N < N then
            (-1 : ℝ)^(j+N) * β j *
              (conj (x ⟨2*j-N,hj.2⟩) * x ⟨N-1, by omega⟩).re
          else 0)
          (4 * (∑ i : Fin N, a i))).symm

theorem radialVandermondeResponsePrefix_hasDerivAt_closed {N : ℕ}
    (a : Fin N → ℝ) (β : ℕ → ℝ) (x : Fin N → ℂ)
    (ha : Function.Injective a) (hN : 0 < N) :
    HasDerivAt (fun t : ℝ => radialVandermondeResponsePrefix a β x t)
      (radialVandermondeFirstCorrectionClosed a β x) 0 := by
  rw [← radialVandermondeResponseFirstCoefficient_eq_closed a β x hN]
  exact radialVandermondeResponsePrefix_hasDerivAt_zero a β x ha hN

def radialVandermondeEvenSupported {N : ℕ} (x : Fin N → ℂ) : Prop :=
  ∀ i : Fin N, Odd (i : ℕ) → x i = 0

def radialVandermondeOddSupported {N : ℕ} (x : Fin N → ℂ) : Prop :=
  ∀ i : Fin N, Even (i : ℕ) → x i = 0

theorem radialVandermondeFirstCorrectionClosed_eq_zero_of_even_supported
    {N : ℕ} (a : Fin N → ℝ) (β : ℕ → ℝ) (x : Fin N → ℂ)
    (hx : radialVandermondeEvenSupported x) :
    radialVandermondeFirstCorrectionClosed a β x = 0 := by
  classical
  unfold radialVandermondeFirstCorrectionClosed
  have hsum : (∑ j ∈ Finset.range N,
      if hj : N ≤ 2*j ∧ 2*j-N < N then
        (-1 : ℝ)^(j+N) * β j *
          (conj (x ⟨2*j-N,hj.2⟩) * x ⟨N-1, by omega⟩).re
      else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hjvalid : N ≤ 2*j ∧ 2*j-N < N
    · rw [dif_pos hjvalid]
      have hN : 0 < N := by omega
      by_cases hNeven : Even N
      · obtain ⟨k,hk⟩ := hNeven
        have hlastOdd : Odd (N-1) := ⟨k-1, by omega⟩
        have hlast : x ⟨N-1, by omega⟩ = 0 := hx _ hlastOdd
        simp [hlast]
      · have hNodd : Odd N := Nat.not_even_iff_odd.mp hNeven
        obtain ⟨n,hn⟩ := hNodd
        have hjn : n+1 ≤ j := by omega
        have hkodd : Odd (2*j-N) := ⟨j-n-1, by omega⟩
        have hk : x ⟨2*j-N,hjvalid.2⟩ = 0 := hx _ hkodd
        simp [hk]
    · rw [dif_neg hjvalid]
  rw [hsum]
  ring

theorem radialVandermondeFirstCorrectionClosed_eq_zero_of_odd_supported
    {N : ℕ} (a : Fin N → ℝ) (β : ℕ → ℝ) (x : Fin N → ℂ)
    (hx : radialVandermondeOddSupported x) :
    radialVandermondeFirstCorrectionClosed a β x = 0 := by
  classical
  unfold radialVandermondeFirstCorrectionClosed
  have hsum : (∑ j ∈ Finset.range N,
      if hj : N ≤ 2*j ∧ 2*j-N < N then
        (-1 : ℝ)^(j+N) * β j *
          (conj (x ⟨2*j-N,hj.2⟩) * x ⟨N-1, by omega⟩).re
      else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hjvalid : N ≤ 2*j ∧ 2*j-N < N
    · rw [dif_pos hjvalid]
      by_cases hNodd : Odd N
      · obtain ⟨k,hk⟩ := hNodd
        have hlastEven : Even (N-1) := ⟨k, by omega⟩
        have hlast : x ⟨N-1, by omega⟩ = 0 := hx _ hlastEven
        simp [hlast]
      · have hNeven : Even N := Nat.not_odd_iff_even.mp hNodd
        obtain ⟨n,hn⟩ := hNeven
        have hjn : n ≤ j := by omega
        have hkeven : Even (2*j-N) := ⟨j-n, by omega⟩
        have hk : x ⟨2*j-N,hjvalid.2⟩ = 0 := hx _ hkeven
        simp [hk]
    · rw [dif_neg hjvalid]
  rw [hsum]
  ring

theorem radialVandermondeFirstCorrectionClosed_one_eq_zero
    (a : Fin 1 → ℝ) (β : ℕ → ℝ) (x : Fin 1 → ℂ) :
    radialVandermondeFirstCorrectionClosed a β x = 0 := by
  simp [radialVandermondeFirstCorrectionClosed]

/-- The first-order coefficient vector, before pairing with the final boundary
coordinate. Its coordinates collect all admissible reflected indices. -/
def radialVandermondeFirstCorrectionVector {N : ℕ} (a : Fin N → ℝ)
    (β : ℕ → ℝ) : Fin N → ℝ := fun i =>
  2 * (∑ k : Fin N, a k) * (∑ j ∈ Finset.range N,
    if hj : N ≤ 2*j ∧ 2*j-N < N then
      if i = ⟨2*j-N,hj.2⟩ then (-1 : ℝ)^(j+N) * β j else 0
    else 0)

/-- The last coordinate vector in the boundary space. -/
def radialVandermondeLastUnit {N : ℕ} : Fin N → ℝ :=
  fun i => if (i : ℕ) = N-1 then 1 else 0

/-- Symmetric rank-two outer-product matrix for the first correction. -/
def radialVandermondeFirstCorrectionMatrix {N : ℕ} (a : Fin N → ℝ)
    (β : ℕ → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.vecMulVec (radialVandermondeFirstCorrectionVector a β)
      radialVandermondeLastUnit +
    Matrix.vecMulVec radialVandermondeLastUnit
      (radialVandermondeFirstCorrectionVector a β)

/-- The real Hermitian quadratic form associated with a real matrix. -/
def radialVandermondeRealMatrixForm {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ)
    (x : Fin N → ℂ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, M i j * (conj (x i) * x j).re

/-- The correction matrix has rank at most two, directly from its two
outer-product columns. -/
theorem radialVandermondeFirstCorrectionMatrix_rank_le_two {N : ℕ}
    (a : Fin N → ℝ) (β : ℕ → ℝ) :
    (radialVandermondeFirstCorrectionMatrix a β).rank ≤ 2 := by
  classical
  let u := radialVandermondeFirstCorrectionVector a β
  let e : Fin N → ℝ := radialVandermondeLastUnit (N := N)
  let pair : Finset (Fin N → ℝ) := {u,e}
  let W : Submodule ℝ (Fin N → ℝ) := Submodule.span ℝ (pair : Set (Fin N → ℝ))
  have hu : u ∈ W := Submodule.subset_span (by simp [pair])
  have he : e ∈ W := Submodule.subset_span (by simp [pair])
  have hcols : Set.range (radialVandermondeFirstCorrectionMatrix a β).col ⊆ W := by
    rintro v ⟨j,rfl⟩
    have hcol : (radialVandermondeFirstCorrectionMatrix a β).col j =
        (e j) • u + (u j) • e := by
      ext i
      simp [radialVandermondeFirstCorrectionMatrix, u, e,
        Matrix.col_apply, Matrix.vecMulVec_apply]
      ring
    rw [hcol]
    exact W.add_mem (W.smul_mem (e j) hu) (W.smul_mem (u j) he)
  have hspan : Submodule.span ℝ
      (Set.range (radialVandermondeFirstCorrectionMatrix a β).col) ≤ W :=
    Submodule.span_le.2 hcols
  rw [Matrix.rank_eq_finrank_span_cols]
  have hfinset := finrank_span_finset_le_card (R := ℝ) pair
  have hcard : pair.card ≤ 2 := by
    calc
      _ ≤ ({e} : Finset (Fin N → ℝ)).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  have hdim : Module.finrank ℝ W ≤ 2 := by
    change Module.finrank ℝ (Submodule.span ℝ (pair : Set (Fin N → ℝ))) ≤ 2
    exact hfinset.trans hcard
  exact (Submodule.finrank_mono hspan).trans hdim

private theorem radialVandermondeDelta_sum {N : ℕ} (k : Fin N)
    (c : ℝ) (f : Fin N → ℝ) :
    (∑ i : Fin N, (if i = k then c else 0) * f i) = c * f k := by
  classical
  rw [Finset.sum_eq_single k]
  · simp
  · intro i hi hik
    simp [hik]
  · intro hk
    exact False.elim (hk (Finset.mem_univ k))

private theorem radialVandermondeFirstCorrectionVector_pairing {N : ℕ}
    (a : Fin N → ℝ) (β : ℕ → ℝ) (x : Fin N → ℂ) (hN : 0 < N) :
    (∑ i : Fin N, radialVandermondeFirstCorrectionVector a β i *
      (conj (x i) * x ⟨N-1, by omega⟩).re) =
      2 * (∑ i : Fin N, a i) *
        ∑ j ∈ Finset.range N,
          if hj : N ≤ 2*j ∧ 2*j-N < N then
            (-1 : ℝ)^(j+N) * β j *
              (conj (x ⟨2*j-N,hj.2⟩) * x ⟨N-1, by omega⟩).re
          else 0 := by
  classical
  let last : Fin N := ⟨N-1, by omega⟩
  let f : Fin N → ℝ := fun i => (conj (x i) * x last).re
  let c : ℝ := 2 * ∑ i : Fin N, a i
  have hfactor : (∑ i : Fin N, c *
      ((∑ j ∈ Finset.range N,
        if hj : N ≤ 2*j ∧ 2*j-N < N then
          if i = ⟨2*j-N,hj.2⟩ then (-1 : ℝ)^(j+N) * β j else 0
        else 0) * f i)) =
      c * ∑ i : Fin N, ∑ j ∈ Finset.range N,
        (if hj : N ≤ 2*j ∧ 2*j-N < N then
          if i = ⟨2*j-N,hj.2⟩ then (-1 : ℝ)^(j+N) * β j else 0
        else 0) * f i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_mul]
  have hinner (j : ℕ) :
      (∑ i : Fin N,
        (if hj : N ≤ 2*j ∧ 2*j-N < N then
          if i = ⟨2*j-N,hj.2⟩ then (-1 : ℝ)^(j+N) * β j else 0
        else 0) * f i) =
      if hj : N ≤ 2*j ∧ 2*j-N < N then
        (-1 : ℝ)^(j+N) * β j * f ⟨2*j-N,hj.2⟩ else 0 := by
    by_cases hj : N ≤ 2*j ∧ 2*j-N < N
    · simp only [dif_pos hj]
      exact radialVandermondeDelta_sum ⟨2*j-N,hj.2⟩
        ((-1 : ℝ)^(j+N) * β j) f
    · simp only [dif_neg hj, zero_mul, Finset.sum_const_zero]
  unfold radialVandermondeFirstCorrectionVector
  calc
    _ = ∑ i : Fin N, c *
        ((∑ j ∈ Finset.range N,
          if hj : N ≤ 2*j ∧ 2*j-N < N then
            if i = ⟨2*j-N,hj.2⟩ then (-1 : ℝ)^(j+N) * β j else 0
          else 0) * f i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [c, f, last]
      ring
    _ = c * ∑ i : Fin N, ∑ j ∈ Finset.range N,
        (if hj : N ≤ 2*j ∧ 2*j-N < N then
          if i = ⟨2*j-N,hj.2⟩ then (-1 : ℝ)^(j+N) * β j else 0
        else 0) * f i := hfactor
    _ = c * ∑ j ∈ Finset.range N, ∑ i : Fin N,
        (if hj : N ≤ 2*j ∧ 2*j-N < N then
          if i = ⟨2*j-N,hj.2⟩ then (-1 : ℝ)^(j+N) * β j else 0
        else 0) * f i := by rw [Finset.sum_comm]
    _ = c * ∑ j ∈ Finset.range N,
        (if hj : N ≤ 2*j ∧ 2*j-N < N then
          (-1 : ℝ)^(j+N) * β j * f ⟨2*j-N,hj.2⟩
        else 0) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact hinner j
    _ = _ := by simp [c, f, last]

theorem radialVandermondeFirstCorrectionMatrixForm_eq_closed {N : ℕ}
    (a : Fin N → ℝ) (β : ℕ → ℝ) (x : Fin N → ℂ) (hN : 0 < N) :
    radialVandermondeRealMatrixForm (radialVandermondeFirstCorrectionMatrix a β) x =
      radialVandermondeFirstCorrectionClosed a β x := by
  classical
  let u := radialVandermondeFirstCorrectionVector a β
  let e : Fin N → ℝ := radialVandermondeLastUnit (N := N)
  let last : Fin N := ⟨N-1, by omega⟩
  let cross : Fin N → Fin N → ℝ := fun i j => (conj (x i) * x j).re
  have he (i : Fin N) : e i = if i = last then 1 else 0 := by
    by_cases hi : i = last
    · subst i
      simp [e, radialVandermondeLastUnit, last]
    · have hval : (i : ℕ) ≠ N-1 := by
        intro h
        apply hi
        apply Fin.ext
        simpa [last] using h
      simp [e, radialVandermondeLastUnit, last, hi, hval]
  have hfirst : (∑ i : Fin N, ∑ j : Fin N,
      (u i * e j) * cross i j) = ∑ i : Fin N, u i * cross i last := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = ∑ j : Fin N, if j = last then u i * cross i last else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [he j]
        split_ifs with hjlast
        · subst j
          simp [cross]
        · simp
      _ = u i * cross i last := by simp
  have hsecond : (∑ i : Fin N, ∑ j : Fin N,
      (e i * u j) * cross i j) = ∑ j : Fin N, u j * cross last j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    calc
      _ = ∑ i : Fin N, if i = last then u j * cross last j else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [he i]
        split_ifs with hilast
        · subst i
          simp [cross]
        · simp
      _ = u j * cross last j := by simp
  have hcross : (∑ j : Fin N, u j * cross last j) =
      ∑ j : Fin N, u j * cross j last := by
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (fun r : ℝ => u j * r)
      (radialVandermondeRealCross_swap (x last) (x j))
  have hdecomp : radialVandermondeRealMatrixForm
      (radialVandermondeFirstCorrectionMatrix a β) x =
      (∑ i : Fin N, ∑ j : Fin N, (u i * e j) * cross i j) +
        (∑ i : Fin N, ∑ j : Fin N, (e i * u j) * cross i j) := by
    change (∑ i : Fin N, ∑ j : Fin N,
      ((u i * e j + e i * u j) * cross i j)) = _
    simp_rw [add_mul]
    simp only [Finset.sum_add_distrib]
  rw [hdecomp, hfirst, hsecond, hcross]
  rw [← two_mul (∑ i : Fin N, u i * cross i last)]
  unfold radialVandermondeFirstCorrectionClosed
  rw [radialVandermondeFirstCorrectionVector_pairing a β x hN]
  ring

private def radialSevenVandermondeNodes : Fin 7 → ℝ :=
  fun i => (((i : ℕ)+1 : ℕ) : ℝ)

private theorem radialSevenVandermondeNodes_injective :
    Function.Injective radialSevenVandermondeNodes := by
  intro i j hij
  apply Fin.ext
  have hv : (i : ℝ) + 1 = (j : ℝ) + 1 := by
    simpa [radialSevenVandermondeNodes] using hij
  have hv' : (i : ℝ) = (j : ℝ) := by linarith
  exact_mod_cast hv'

/-- The source chart inverse is exactly the inverse of the Vandermonde matrix
at the original nodes 1,…,7. This identifies the finite-step charts, not only
their limiting faces. -/
theorem radialSevenSourceInverse_eq_radialVandermondeInverse :
    radialVandermondeInverse radialSevenVandermondeNodes =
      radialSevenBoundaryInverseCoefficients := by
  classical
  let Q : Matrix (Fin 7) (Fin 7) ℝ := fun i j => radialSevenBoundaryInverseCoefficients i j
  have hright : radialVandermondeMatrix radialSevenVandermondeNodes * Q = 1 := by
    ext r j
    change (∑ i : Fin 7, radialSevenVandermondeNodes i ^ (r : ℕ) *
      radialSevenBoundaryInverseCoefficients i j) = if r = j then 1 else 0
    fin_cases r <;> fin_cases j <;>
      norm_num [radialSevenVandermondeNodes,
        radialSevenBoundaryInverseCoefficients, Fin.sum_univ_succ]
  have hinv := Matrix.inv_eq_right_inv hright
  simpa [radialVandermondeInverse, Q] using hinv

/-- The general Vandermonde coordinates at 1,…,7 are the original physical
regularized boundary coordinates. -/
theorem radialSevenBoundaryCoordinate_eq_radialVandermonde
    (h : ℝ) (x : Fin 7 → ℂ) (m : ℕ) :
    radialVandermondeBoundaryCoordinate radialSevenVandermondeNodes x h m =
      radialSevenRegularizedBoundary h x m := by
  classical
  unfold radialVandermondeBoundaryCoordinate radialSevenRegularizedBoundary
  split_ifs with hm
  · rfl
  · unfold radialVandermondeHighCoordinate radialSevenHigherBoundaryCoefficient
    rw [radialSevenSourceInverse_eq_radialVandermondeInverse]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [radialSevenVandermondeNodes]
    ring

/-- The finite N=7 response is the original full physical boundary storage.
The outer factor 2 is present on both sides; in the native source coefficients
β_j is already `2 h_j`. No moment-fitted chart is substituted. -/
theorem radialSevenPhysicalResponsePrefix_eq_storage
    (h : ℝ) (x : Fin 7 → ℂ) :
    radialVandermondeResponsePrefix radialSevenVandermondeNodes
        nativeSourceOddBoundaryCoefficient x h =
      radialSevenRegularizedBoundaryEnergy h x := by
  unfold radialVandermondeResponsePrefix radialSevenRegularizedBoundaryEnergy
  simp_rw [radialSevenBoundaryCoordinate_eq_radialVandermonde]

theorem radialSevenNativeCoefficient_factor_two (j : ℕ) :
    nativeSourceOddBoundaryCoefficient j =
      2 * primeDepthGeometricMoment j := by
  exact nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment j

/-- The existing seven-sample boundary derivative is recovered by the general
Vandermonde first-correction theorem through the identical physical chart. -/
theorem radialSevenPhysicalStorage_hasDerivAt_from_all_order (x : Fin 7 → ℂ) :
    HasDerivAt (fun h : ℝ => radialSevenRegularizedBoundaryEnergy h x)
      (radialVandermondeFirstCorrectionClosed radialSevenVandermondeNodes
        nativeSourceOddBoundaryCoefficient x) 0 := by
  simpa only [← radialSevenPhysicalResponsePrefix_eq_storage] using
    radialVandermondeResponsePrefix_hasDerivAt_closed
      radialSevenVandermondeNodes nativeSourceOddBoundaryCoefficient x
      radialSevenVandermondeNodes_injective (by norm_num)

theorem radialVandermondeFirstCorrectionClosed_seven_eq_existing
    (x : Fin 7 → ℂ) :
    radialVandermondeFirstCorrectionClosed
      (fun i : Fin 7 => (((i : ℕ)+1 : ℕ) : ℝ))
      nativeSourceOddBoundaryCoefficient x = radialSevenBoundaryFirstCorrection x := by
  have he₁ : (∑ i : Fin 7, (((i : ℕ)+1 : ℕ) : ℝ)) = 28 := by
    norm_num [Fin.sum_univ_succ]
  unfold radialVandermondeFirstCorrectionClosed radialSevenBoundaryFirstCorrection
  rw [he₁]
  norm_num [Finset.sum_range_succ, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  have h1 : (⟨1, by omega⟩ : Fin 7) = 1 := by apply Fin.ext; rfl
  have h3 : (⟨3, by omega⟩ : Fin 7) = 3 := by apply Fin.ext; rfl
  have h5 : (⟨5, by omega⟩ : Fin 7) = 5 := by apply Fin.ext; rfl
  have h6 : (⟨6, by omega⟩ : Fin 7) = 6 := by apply Fin.ext; rfl
  simp only [h3, h5, h6]
  ring

end
end CarrySelfAdjointOperator
