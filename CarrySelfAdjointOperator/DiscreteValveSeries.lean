import CarrySelfAdjointOperator.DiscreteValve

/-!
# O bracket aditivo como `(1-X)²` no anel de séries formais

Os operadores de diferença da válvula aditiva, levados à geradora `R⟦X⟧`, são
multiplicação por potências de `(1 - X)` (a menos do bordo): a primeira diferença
`fdiff` é `(1 - X)·`, e o bracket (segunda diferença) é `(1 - X)²·`. Isso põe o
operador da válvula aditiva no **mesmo anel** `R⟦X⟧` onde vive a log-derivada
`X · d/dX` da válvula multiplicativa, conectando as duas geometrias sem alvo.
-/

namespace CarrySelfAdjointOperator.DiscreteValve

open PowerSeries

variable {R : Type*} [CommRing R]

/-- A primeira diferença é `(1 - X)·` na geradora (a menos do bordo):
`X · mk (fdiff f) = (1 - X) · mk f - C (f 0)`. -/
theorem X_mul_mk_fdiff (f : ℕ → R) :
    X * mk (fdiff f) = (1 - X) * mk f - C (f 0) := by
  ext n
  cases n with
  | zero => simp
  | succ m =>
    simp only [sub_mul, one_mul, map_sub, coeff_succ_X_mul, coeff_mk, coeff_C,
      Nat.succ_ne_zero, ↓reduceIte, fdiff, sub_zero]

/-- **O bracket é `(1 - X)²·` na geradora.** A segunda diferença da válvula
aditiva, no anel `R⟦X⟧`, é multiplicação por `(1 - X)²` (a menos do bordo de
grau `1`): `X² · mk (bracket f) = (1-X)² · mk f - (1-X)·C(f 0) - X·C(fdiff f 0)`.
O inverso, `1/(1-X)² = ∑ (n+1) Xⁿ`, é exatamente o núcleo de Green `greenSum`.
Assim o operador da válvula aditiva vive no mesmo anel que a log-derivada
`X·d/dX` da válvula multiplicativa. -/
theorem X_sq_mul_mk_bracket (f : ℕ → R) :
    X ^ 2 * mk (bracket f)
      = (1 - X) ^ 2 * mk f - (1 - X) * C (f 0) - X * C (fdiff f 0) := by
  have hb : bracket f = fdiff (fdiff f) := by
    funext j; rw [bracket_eq_fdiff_sub]; rfl
  rw [hb]
  linear_combination (X : R⟦X⟧) * X_mul_mk_fdiff (fdiff f) + (1 - X) * X_mul_mk_fdiff f

/-! ## Teorema da série de Green -/

/-- Série geométrica `1/(1-X) = ∑ Xⁿ`. -/
def geometricSeries : PowerSeries R := mk fun _ => 1

/-- Núcleo de Green `1/(1-X)² = ∑ (n+1) Xⁿ`. -/
def greenKernelSeries : PowerSeries R := mk fun n => (n : R) + 1

/-- `(1 - X)` inverte a série geométrica. -/
theorem one_sub_X_mul_geometricSeries : (1 - X) * geometricSeries = (1 : R⟦X⟧) := by
  ext n
  cases n with
  | zero => simp [geometricSeries]
  | succ m =>
    simp only [geometricSeries, sub_mul, one_mul, map_sub, coeff_succ_X_mul,
      coeff_mk, coeff_one, Nat.succ_ne_zero, ↓reduceIte, sub_self]

/-- `(1 - X)` desce o núcleo de Green para a série geométrica. -/
theorem one_sub_X_mul_greenKernelSeries :
    (1 - X) * greenKernelSeries = (geometricSeries : R⟦X⟧) := by
  ext n
  cases n with
  | zero => simp [greenKernelSeries, geometricSeries]
  | succ m =>
    simp only [greenKernelSeries, geometricSeries, sub_mul, one_mul, map_sub,
      coeff_succ_X_mul, coeff_mk]
    push_cast; ring

/-- **`(1 - X)² · greenKernelSeries = 1`.** O núcleo de Green é o inverso formal
de `(1-X)²`: `1/(1-X)² = ∑ (n+1) Xⁿ`. -/
theorem one_sub_X_sq_mul_greenKernelSeries :
    (1 - X) ^ 2 * greenKernelSeries = (1 : R⟦X⟧) := by
  rw [sq, mul_assoc, one_sub_X_mul_greenKernelSeries, one_sub_X_mul_geometricSeries]

/-- `X · greenKernelSeries = ∑ n Xⁿ` (a série de graus). -/
theorem X_mul_greenKernelSeries :
    X * greenKernelSeries = mk (fun m => (m : R)) := by
  ext n
  cases n with
  | zero => simp [greenKernelSeries]
  | succ m =>
    simp only [greenKernelSeries, coeff_succ_X_mul, coeff_mk]
    push_cast; ring

/-- **A integral de Green é `X/(1-X)²·` na geradora.**
`mk (greenSum f) = X · greenKernelSeries · mk (bracket f)`, i.e.
`mk(𝒢 (Bf)) = X/(1-X)² · mk(Bf)`: a soma de Green é convolução com o núcleo. -/
theorem mk_greenSum (f : ℕ → R) :
    mk (fun n => greenSum f n) = X * greenKernelSeries * mk (bracket f) := by
  rw [X_mul_greenKernelSeries]
  ext n
  rw [coeff_mk, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_mk, greenSum]
  rw [← Finset.sum_range_reflect (fun i => (i : R) * bracket f (n - i)) (n + 1),
    Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < n := Finset.mem_range.mp hi
  rw [nsmul_eq_mul, Nat.sub_sub_self (le_of_lt hi')]

/-- **Teorema Fundamental da Válvula Discreta em séries formais.** A reconstrução
inteira do estado como uma igualdade em `R⟦X⟧`:
`F = f₀/(1-X) + X·Δf₀/(1-X)² + X²·B(X)/(1-X)²`, os três canais — valor de bordo,
inclinação de bordo, e curvatura — resolvidos algebricamente. Equivale à
telescopagem em sequências (`discrete_valve`). -/
theorem mk_discrete_valve (f : ℕ → R) :
    mk f = C (f 0) * geometricSeries + X * C (fdiff f 0) * greenKernelSeries
      + X ^ 2 * greenKernelSeries * mk (bracket f) := by
  rw [← one_sub_X_mul_greenKernelSeries]
  linear_combination (-greenKernelSeries) * X_sq_mul_mk_bracket f
    - mk f * one_sub_X_sq_mul_greenKernelSeries (R := R)

end CarrySelfAdjointOperator.DiscreteValve
