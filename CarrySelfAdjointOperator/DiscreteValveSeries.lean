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

end CarrySelfAdjointOperator.DiscreteValve
