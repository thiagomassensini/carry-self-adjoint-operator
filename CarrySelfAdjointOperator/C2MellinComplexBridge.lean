import NativeCarrySpectralWeyl.Camera.BracketSeries
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

open Set MeasureTheory
open scoped BigOperators

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Camera
open FiniteNativeCarryOperator.Camera

noncomputable section
set_option autoImplicit false

/-- The complex Mellin integrand of one exponential with positive real rate. -/
def nativeC2MellinComplexRateIntegrand (s : ℂ) (r : ℝ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (s - 1) * Complex.exp (-((r : ℂ) * (x : ℂ)))

/-- Integrability of each exponential Mellin leg, proved by scaling the
convergent Euler integral for Gamma. -/
theorem nativeC2MellinComplexRateIntegrable {s : ℂ} (hs : 0 < s.re)
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn (nativeC2MellinComplexRateIntegrand s r) (Ioi 0) := by
  let g : ℝ → ℂ := fun y => (Real.exp (-y) : ℂ) * (y : ℂ) ^ (s - 1)
  have hbase : IntegrableOn g (Ioi 0) := by
    simpa [g] using Complex.GammaIntegral_convergent hs
  have hbase' : IntegrableOn g (Ioi (r * 0)) := by simpa using hbase
  have hcomp : IntegrableOn (fun x : ℝ => g (r * x)) (Ioi 0) := by
    simpa [mul_zero] using
      (integrableOn_Ioi_comp_mul_left_iff g 0 hr).2 hbase'
  have hscale : IntegrableOn
      (fun x : ℝ => (r : ℂ) ^ (-(s - 1)) * g (r * x)) (Ioi 0) := by
    change Integrable (fun x : ℝ => (r : ℂ) ^ (-(s - 1)) * g (r * x))
      (volume.restrict (Ioi 0))
    exact hcomp.const_mul _
  apply (integrableOn_congr_fun (s := Ioi 0) ?_ measurableSet_Ioi).mpr hscale
  intro x hx
  have hx0 : 0 ≤ x := le_of_lt hx
  have hmul := Complex.mul_cpow_ofReal_nonneg hr.le hx0 (s - 1)
  dsimp [nativeC2MellinComplexRateIntegrand, g]
  rw [Complex.ofReal_mul, hmul, Complex.ofReal_exp, Complex.cpow_neg]
  field_simp [Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr hr.ne'))]
  congr 1
  push_cast
  ring

private theorem ofReal_invRate {r : ℝ} :
    ((1 / r : ℝ) : ℂ) = 1 / (r : ℂ) := by
  rw [Complex.ofReal_div]
  simp

private theorem invRate_cpow {s : ℂ} {r : ℝ} (hr : 0 < r) :
    ((1 / r : ℝ) : ℂ) ^ s = (r : ℂ) ^ (-s) := by
  have harg : (r : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hr.le]
    exact Real.pi_ne_zero.symm
  calc
    ((1 / r : ℝ) : ℂ) ^ s = (1 / (r : ℂ)) ^ s := by
      rw [ofReal_invRate]
    _ = ((r : ℂ) ^ s)⁻¹ := by
      rw [one_div, Complex.inv_cpow _ _ harg]
    _ = (r : ℂ) ^ (-s) := (Complex.cpow_neg _ _).symm

/-- Mellin's integral for one exponential leg, with its value written as a
complex negative power. -/
theorem nativeC2MellinComplexRateIntegral {s : ℂ} (hs : 0 < s.re)
    {r : ℝ} (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ), nativeC2MellinComplexRateIntegrand s r x) =
      (r : ℂ) ^ (-s) * Complex.Gamma s := by
  change (∫ x in Ioi (0 : ℝ),
      (x : ℂ) ^ (s - 1) * Complex.exp (-((r : ℂ) * (x : ℂ)))) =
    (r : ℂ) ^ (-s) * Complex.Gamma s
  calc
    _ = (1 / (r : ℂ)) ^ s * Complex.Gamma s :=
      Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr
    _ = ((1 / r : ℝ) : ℂ) ^ s * Complex.Gamma s := by
      rw [← ofReal_invRate]
    _ = (r : ℂ) ^ (-s) * Complex.Gamma s := by
      rw [invRate_cpow hr]

def nativeC2MellinComplexBracketIntegrand (s : ℂ) (c x : ℝ) : ℂ :=
  nativeC2MellinComplexRateIntegrand s (c - 1) x -
    2 * nativeC2MellinComplexRateIntegrand s c x +
    nativeC2MellinComplexRateIntegrand s (c + 1) x

theorem nativeC2MellinComplexBracketIntegrand_eq_kernel {s : ℂ} (c x : ℝ) :
    nativeC2MellinComplexBracketIntegrand s c x =
      (x : ℂ) ^ (s - 1) *
        (Complex.exp (-(((c - 1 : ℝ) : ℂ) * (x : ℂ))) -
          2 * Complex.exp (-((c : ℂ) * (x : ℂ))) +
          Complex.exp (-(((c + 1 : ℝ) : ℂ) * (x : ℂ)))) := by
  simp [nativeC2MellinComplexBracketIntegrand,
    nativeC2MellinComplexRateIntegrand]
  ring

private theorem nativeC2MellinComplexBracketIntegrable {s : ℂ}
    (hs : 0 < s.re) {c : ℝ} (hc : 1 < c) :
    IntegrableOn (nativeC2MellinComplexBracketIntegrand s c) (Ioi 0) := by
  have hleft : IntegrableOn
      (nativeC2MellinComplexRateIntegrand s (c - 1)) (Ioi 0) :=
    nativeC2MellinComplexRateIntegrable hs (by linarith)
  have hmid : IntegrableOn
      (nativeC2MellinComplexRateIntegrand s c) (Ioi 0) :=
    nativeC2MellinComplexRateIntegrable hs (by linarith)
  have hright : IntegrableOn
      (nativeC2MellinComplexRateIntegrand s (c + 1)) (Ioi 0) :=
    nativeC2MellinComplexRateIntegrable hs (by linarith)
  have hmid' : IntegrableOn
      (fun x => (2 : ℂ) * nativeC2MellinComplexRateIntegrand s c x) (Ioi 0) :=
    hmid.const_mul 2
  exact (hleft.sub hmid').add hright

/-- Exact complex Mellin identity for a centered bracket. No positivity
assumption is used: only `Re(s) > 0`, which makes all three Euler integrals
converge. -/
theorem nativeC2MellinComplexBracketIntegral {s : ℂ} (hs : 0 < s.re)
    {c : ℝ} (hc : 1 < c) :
    (∫ x in Ioi (0 : ℝ), nativeC2MellinComplexBracketIntegrand s c x) =
      Complex.Gamma s *
        (((c - 1 : ℝ) : ℂ) ^ (-s) - 2 * (c : ℂ) ^ (-s) +
          ((c + 1 : ℝ) : ℂ) ^ (-s)) := by
  have hleft : 0 < c - 1 := by linarith
  have hmid : 0 < c := by linarith
  have hright : 0 < c + 1 := by linarith
  have h₁ := nativeC2MellinComplexRateIntegrable hs hleft
  have h₂ := nativeC2MellinComplexRateIntegrable hs hmid
  have h₃ := nativeC2MellinComplexRateIntegrable hs hright
  have h₂' : IntegrableOn
      (fun x => (2 : ℂ) * nativeC2MellinComplexRateIntegrand s c x) (Ioi 0) :=
    h₂.const_mul 2
  have hleft' : IntegrableOn
      (fun x => nativeC2MellinComplexRateIntegrand s (c - 1) x -
        2 * nativeC2MellinComplexRateIntegrand s c x) (Ioi 0) :=
    h₁.sub h₂'
  calc
    _ = (∫ x in Ioi (0 : ℝ),
          nativeC2MellinComplexRateIntegrand s (c - 1) x -
            2 * nativeC2MellinComplexRateIntegrand s c x) +
        ∫ x in Ioi (0 : ℝ), nativeC2MellinComplexRateIntegrand s (c + 1) x :=
          integral_add hleft' h₃
    _ = ((∫ x in Ioi (0 : ℝ), nativeC2MellinComplexRateIntegrand s (c - 1) x) -
          ∫ x in Ioi (0 : ℝ),
            (2 : ℂ) * nativeC2MellinComplexRateIntegrand s c x) +
        ∫ x in Ioi (0 : ℝ), nativeC2MellinComplexRateIntegrand s (c + 1) x := by
          rw [integral_sub h₁ h₂']
    _ = ((∫ x in Ioi (0 : ℝ), nativeC2MellinComplexRateIntegrand s (c - 1) x) -
          (2 : ℂ) * ∫ x in Ioi (0 : ℝ),
            nativeC2MellinComplexRateIntegrand s c x) +
        ∫ x in Ioi (0 : ℝ), nativeC2MellinComplexRateIntegrand s (c + 1) x := by
          rw [integral_const_mul]
    _ = _ := by
          rw [nativeC2MellinComplexRateIntegral hs (by linarith : 0 < c - 1),
            nativeC2MellinComplexRateIntegral hs (by linarith : 0 < c),
            nativeC2MellinComplexRateIntegral hs (by linarith : 0 < c + 1)]
          ring

/-- Exponential form of the positive C2 cell kernel. -/
theorem nativeC2MellinCellKernel_eq_centered_exponentials (c x : ℝ) :
    Real.exp (-(c * x)) * (4 * Real.sinh (x / 2) ^ 2) =
      Real.exp (-((c - 1) * x)) - 2 * Real.exp (-(c * x)) +
        Real.exp (-((c + 1) * x)) := by
  have hhalf : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hpos : Real.exp (x / 2) ^ 2 = Real.exp x := by
    calc
      Real.exp (x / 2) ^ 2 = Real.exp (x / 2) * Real.exp (x / 2) := by ring
      _ = Real.exp x := by rw [← Real.exp_add]; congr 1; ring
  have hneg : Real.exp (-(x / 2)) ^ 2 = Real.exp (-x) := by
    calc
      Real.exp (-(x / 2)) ^ 2 =
          Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by ring
      _ = Real.exp (-x) := by rw [← Real.exp_add]; congr 1; ring
  have hsinh : 4 * Real.sinh (x / 2) ^ 2 = Real.exp x - 2 + Real.exp (-x) := by
    rw [Real.sinh_eq]
    have hsq : 4 * ((Real.exp (x / 2) - Real.exp (-(x / 2))) / 2) ^ 2 =
        Real.exp (x / 2) ^ 2 -
          2 * (Real.exp (x / 2) * Real.exp (-(x / 2))) +
          Real.exp (-(x / 2)) ^ 2 := by ring
    rw [hsq, hpos, hhalf, hneg]
    ring
  rw [hsinh]
  have hleft : -(c * x) + x = -((c - 1) * x) := by ring
  have hright : -(c * x) + -x = -((c + 1) * x) := by ring
  calc
    _ = Real.exp (-(c * x)) * Real.exp x - 2 * Real.exp (-(c * x)) +
          Real.exp (-(c * x)) * Real.exp (-x) := by ring
    _ = Real.exp (-(c * x) + x) - 2 * Real.exp (-(c * x)) +
          Real.exp (-(c * x) + -x) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ = _ := by rw [hleft, hright]

/-- The positive Mellin cell kernel and the bracket's three exponential legs
are the same pointwise integrand after Mellin weighting. -/
theorem nativeC2MellinComplexCellIntegrand_eq_bracket {s : ℂ} (c x : ℝ) :
    (x : ℂ) ^ (s - 1) *
        (Real.exp (-(c * x)) * (4 * Real.sinh (x / 2) ^ 2) : ℝ) =
      nativeC2MellinComplexBracketIntegrand s c x := by
  rw [nativeC2MellinCellKernel_eq_centered_exponentials]
  rw [nativeC2MellinComplexBracketIntegrand_eq_kernel]
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_neg, Complex.ofReal_ofNat, Complex.ofReal_add]

/-- The complex Mellin transform of the original radius-one bracket at a
natural center is exactly its three Dirichlet legs times Gamma. -/
theorem nativeC2MellinComplexNaturalBracketIntegral {s : ℂ}
    (hs : 0 < s.re) {center : ℕ} (hc : 1 < center) :
    (∫ x in Ioi (0 : ℝ),
      nativeC2MellinComplexBracketIntegrand s (center : ℝ) x) =
      Complex.Gamma s * centeredBracketTerm s center 1 := by
  rw [nativeC2MellinComplexBracketIntegral hs (by exact_mod_cast hc)]
  simp [centeredBracketTerm, dirichletValue, Nat.cast_sub hc.le,
    Nat.cast_one, Nat.cast_add, Complex.ofReal_sub, Complex.ofReal_add]

/-- Specialization of the complex Mellin identity to the repository's aligned
C2 center blocks. -/
theorem nativeC2MellinComplexCenterBracketIntegral {s : ℂ}
    (hs : 0 < s.re) (index : ℕ) :
    (∫ x in Ioi (0 : ℝ),
      nativeC2MellinComplexBracketIntegrand s
        ((alignedCenter 2 index : ℕ) : ℝ) x) =
      Complex.Gamma s * centerBracketTerm 2 s index := by
  have hc : 1 < alignedCenter 2 index := by
    rw [alignedCenter_eq_cameraSlope_mul, cameraSlope_two]
    omega
  simpa [centerBracketTerm] using
    (nativeC2MellinComplexNaturalBracketIntegral hs hc)

/-- The source's positive hyperbolic cell at a native C2 center has Mellin
transform Gamma times the original bracket term. -/
theorem nativeC2MellinComplexPositiveCellIntegral {s : ℂ}
    (hs : 0 < s.re) (index : ℕ) :
    (∫ x in Ioi (0 : ℝ),
      (x : ℂ) ^ (s - 1) *
        (Real.exp (-((alignedCenter 2 index : ℕ) * x)) *
          (4 * Real.sinh (x / 2) ^ 2) : ℝ)) =
      Complex.Gamma s * centerBracketTerm 2 s index := by
  calc
    _ = ∫ x in Ioi (0 : ℝ),
          nativeC2MellinComplexBracketIntegrand s
            ((alignedCenter 2 index : ℕ) : ℝ) x := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          exact nativeC2MellinComplexCellIntegrand_eq_bracket _ _
    _ = Complex.Gamma s * centerBracketTerm 2 s index :=
          nativeC2MellinComplexCenterBracketIntegral hs index

/-- The first `M` positive C2 cells sum exactly to the closed geometric
head. This keeps the positive hyperbolic kernel and the original aligned
centers visible. -/
theorem nativeC2MellinFinitePositiveCellSum_eq_geometric (M : ℕ)
    {x : ℝ} (hx : 0 < x) :
    (∑ index ∈ Finset.range M,
      Real.exp (-((alignedCenter 2 index : ℕ) * x)) *
        (4 * Real.sinh (x / 2) ^ 2)) =
      (1 - Real.exp (-((4 : ℝ) * (M : ℝ) * x))) *
        (Real.exp (-4 * x) * (4 * Real.sinh (x / 2) ^ 2) /
          (1 - Real.exp (-4 * x))) := by
  let q : ℝ := Real.exp (-4 * x)
  let K : ℝ := 4 * Real.sinh (x / 2) ^ 2
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := by
    dsimp [q]
    apply Real.exp_lt_one_iff.mpr
    linarith
  have hden : 1 - q ≠ 0 := ne_of_gt (by linarith)
  have hcell (index : ℕ) :
      Real.exp (-((alignedCenter 2 index : ℕ) * x)) = q ^ (index + 1) := by
    rw [alignedCenter_eq_cameraSlope_mul, cameraSlope_two]
    dsimp [q]
    calc
      Real.exp (-((4 * (index + 1) : ℕ) * x)) =
          Real.exp (((index + 1 : ℕ) : ℝ) * (-4 * x)) := by
            congr 1
            push_cast
            ring
      _ = Real.exp (-4 * x) ^ (index + 1) := Real.exp_nat_mul _ _
  have hqM : q ^ M = Real.exp (-((4 : ℝ) * (M : ℝ) * x)) := by
    dsimp [q]
    calc
      Real.exp (-4 * x) ^ M =
          Real.exp ((M : ℝ) * (-4 * x)) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp (-((4 : ℝ) * (M : ℝ) * x)) := by congr 1; ring
  have hgeom' :
      (∑ index ∈ Finset.range M, q ^ index) * (q - 1) + 1 = q ^ M := by
    simpa [sub_add_cancel] using (geom_sum_mul_add (q - 1) M)
  have hgeom :
      (∑ index ∈ Finset.range M, q ^ index) * (1 - q) = 1 - q ^ M := by
    have hlin : (∑ index ∈ Finset.range M, q ^ index) * (q - 1) = q ^ M - 1 :=
      by linarith [hgeom']
    calc
      _ = -((∑ index ∈ Finset.range M, q ^ index) * (q - 1)) := by ring
      _ = -(q ^ M - 1) := by rw [hlin]
      _ = _ := by ring
  have hsum :
      (∑ index ∈ Finset.range M, q ^ (index + 1)) =
        q * ∑ index ∈ Finset.range M, q ^ index := by
    calc
      _ = ∑ index ∈ Finset.range M, q ^ index * q := by
            apply Finset.sum_congr rfl
            intro index hi
            rw [pow_succ]
      _ = (∑ index ∈ Finset.range M, q ^ index) * q := by
            rw [Finset.sum_mul]
      _ = _ := by ring
  have hsumK :
      (∑ index ∈ Finset.range M,
        Real.exp (-((alignedCenter 2 index : ℕ) * x)) * K) =
        q * (∑ index ∈ Finset.range M, q ^ index) * K := by
    calc
      _ = (∑ index ∈ Finset.range M, q ^ (index + 1) * K) := by
            apply Finset.sum_congr rfl
            intro index hi
            rw [hcell index]
      _ = (∑ index ∈ Finset.range M, q ^ (index + 1)) * K := by
            rw [Finset.sum_mul]
      _ = _ := by rw [hsum]
  rw [hsumK, ← hqM]
  change q * (∑ index ∈ Finset.range M, q ^ index) * K =
    (1 - q ^ M) * (q * K / (1 - q))
  rw [← hgeom]
  field_simp [hden]

/-- The finite C2 source head written as its seed plus its first `M` positive
Mellin cells. -/
def nativeC2MellinComplexFiniteHeadIntegrand (M : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  nativeC2MellinComplexRateIntegrand s 1 x +
    ∑ index ∈ Finset.range M,
      (x : ℂ) ^ (s - 1) *
        (Real.exp (-((alignedCenter 2 index : ℕ) * x)) *
          (4 * Real.sinh (x / 2) ^ 2) : ℝ)

/-- Pointwise closed form of the same finite C2 Mellin head. Its cell part is
the geometric factor `(1-exp(-4Mx))*omega₀(x)` with the original positive
hyperbolic kernel `omega₀(x)=exp(-4x)K(x)/(1-exp(-4x))`. -/
theorem nativeC2MellinComplexFiniteHeadIntegrand_eq_closed_form
    (M : ℕ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    nativeC2MellinComplexFiniteHeadIntegrand M s x =
      (x : ℂ) ^ (s - 1) *
        ((Real.exp (-x) +
          (1 - Real.exp (-((4 : ℝ) * (M : ℝ) * x))) *
            (Real.exp (-4 * x) * (4 * Real.sinh (x / 2) ^ 2) /
              (1 - Real.exp (-4 * x))) : ℝ) : ℂ) := by
  let cell : ℕ → ℝ := fun index =>
    Real.exp (-((alignedCenter 2 index : ℕ) * x)) *
      (4 * Real.sinh (x / 2) ^ 2)
  have hsum :
      (∑ index ∈ Finset.range M,
        (x : ℂ) ^ (s - 1) * (cell index : ℂ)) =
      (x : ℂ) ^ (s - 1) *
        ((∑ index ∈ Finset.range M, cell index : ℝ) : ℂ) := by
    calc
      _ = (x : ℂ) ^ (s - 1) *
          ∑ index ∈ Finset.range M, (cell index : ℂ) := by
            rw [← Finset.mul_sum]
      _ = _ := by simp
  have hseed : nativeC2MellinComplexRateIntegrand s 1 x =
      (x : ℂ) ^ (s - 1) * (Real.exp (-x) : ℂ) := by
    simp [nativeC2MellinComplexRateIntegrand, Complex.ofReal_exp]
  unfold nativeC2MellinComplexFiniteHeadIntegrand
  rw [hseed, show (fun index =>
      (x : ℂ) ^ (s - 1) *
        (Real.exp (-((alignedCenter 2 index : ℕ) * x)) *
          (4 * Real.sinh (x / 2) ^ 2) : ℝ)) =
        (fun index => (x : ℂ) ^ (s - 1) * (cell index : ℂ)) by
          funext index
          simp [cell, Complex.ofReal_mul]]
  rw [hsum, nativeC2MellinFinitePositiveCellSum_eq_geometric M hx]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_exp]
  ring

/-- Exact Mellin transform of every finite C2 head, identified with the
repository's original finite bracket characteristic for complex `s` in the
Euler half-plane. This is a finite sum theorem; it uses no infinite
sum/integral interchange. -/
theorem nativeC2MellinComplexFiniteHeadIntegral {s : ℂ} (hs : 0 < s.re)
    (M : ℕ) :
    (∫ x in Ioi (0 : ℝ), nativeC2MellinComplexFiniteHeadIntegrand M s x) =
      Complex.Gamma s * finiteBracketCharacteristic 2 M s := by
  have hseed : IntegrableOn
      (nativeC2MellinComplexRateIntegrand s 1) (Ioi 0) :=
    nativeC2MellinComplexRateIntegrable hs (by norm_num)
  have hcell : ∀ index ∈ Finset.range M,
      IntegrableOn
        (fun x : ℝ => (x : ℂ) ^ (s - 1) *
          (Real.exp (-((alignedCenter 2 index : ℕ) * x)) *
            (4 * Real.sinh (x / 2) ^ 2) : ℝ)) (Ioi 0) := by
    intro index _
    have hcenter : 1 < (alignedCenter 2 index : ℝ) := by
      rw [alignedCenter_eq_cameraSlope_mul, cameraSlope_two]
      exact_mod_cast (by omega : 1 < 4 * (index + 1))
    apply (integrableOn_congr_fun (s := Ioi 0)
      (fun x hx => nativeC2MellinComplexCellIntegrand_eq_bracket _ _)
      measurableSet_Ioi).mpr
    exact nativeC2MellinComplexBracketIntegrable hs hcenter
  have hsum : IntegrableOn
      (fun x : ℝ => ∑ index ∈ Finset.range M,
        (x : ℂ) ^ (s - 1) *
          (Real.exp (-((alignedCenter 2 index : ℕ) * x)) *
            (4 * Real.sinh (x / 2) ^ 2) : ℝ)) (Ioi 0) := by
    apply integrable_finsetSum
    intro index hi
    exact hcell index hi
  calc
    _ = (∫ x in Ioi (0 : ℝ), nativeC2MellinComplexRateIntegrand s 1 x) +
        ∫ x in Ioi (0 : ℝ),
          ∑ index ∈ Finset.range M,
            (x : ℂ) ^ (s - 1) *
              (Real.exp (-((alignedCenter 2 index : ℕ) * x)) *
                (4 * Real.sinh (x / 2) ^ 2) : ℝ) := by
          exact integral_add hseed hsum
    _ = (∫ x in Ioi (0 : ℝ), nativeC2MellinComplexRateIntegrand s 1 x) +
        ∑ index ∈ Finset.range M,
          ∫ x in Ioi (0 : ℝ),
            (x : ℂ) ^ (s - 1) *
              (Real.exp (-((alignedCenter 2 index : ℕ) * x)) *
                (4 * Real.sinh (x / 2) ^ 2) : ℝ) := by
          rw [integral_finsetSum (Finset.range M) hcell]
    _ = Complex.Gamma s * finiteBracketCharacteristic 2 M s := by
          simp_rw [nativeC2MellinComplexPositiveCellIntegral hs,
            nativeC2MellinComplexRateIntegral hs (r := 1) (by norm_num)]
          simp [finiteBracketCharacteristic, seedDirichletTerm,
            centerBracketTerm, centeredBracketTerm, dirichletValue]
          rw [← Finset.mul_sum]
          ring

end

end CarrySelfAdjointOperator
