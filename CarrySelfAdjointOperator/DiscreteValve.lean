import Mathlib

/-!
# Teorema Fundamental da Válvula Discreta (TFVD)

Identidade finita **incondicional**: todo estado discreto é a soma exata da
integral de Green da sua curvatura (segunda diferença / bracket) com o retorno
afim do seu traço de bordo (valor + inclinação inicial):

`f = R (Tr f) + G (B f)`,   equivalentemente   `I = G ∘ B + R ∘ Tr`.

É o análogo discreto de `f(x) = f(0) + x f'(0) + ∫₀ˣ (x-t) f''(t) dt`.
Álgebra finita pura sobre qualquer `AddCommGroup`; sem análise, sem zeta, sem RH.
-/

namespace CarrySelfAdjointOperator.DiscreteValve

variable {E : Type*} [AddCommGroup E]

/-- Primeira diferença `(Δf)_k = f_{k+1} - f_k`. -/
def fdiff (f : ℕ → E) (k : ℕ) : E := f (k + 1) - f k

/-- Segunda diferença / bracket (curvatura discreta)
`(B f)_j = f_{j+2} - 2 f_{j+1} + f_j`. -/
def bracket (f : ℕ → E) (j : ℕ) : E := f (j + 2) - 2 • f (j + 1) + f j

/-- O bracket é a primeira diferença da primeira diferença. -/
theorem bracket_eq_fdiff_sub (f : ℕ → E) (j : ℕ) :
    bracket f j = fdiff f (j + 1) - fdiff f j := by
  simp only [bracket, fdiff, two_smul]; abel

/-- Integral de Green discreta do bracket, na forma `f (n+1)`:
`(G (B f)) n = ∑_{j<n} (n - j) • (B f)_j`. -/
def greenSum (f : ℕ → E) (n : ℕ) : E :=
  ∑ j ∈ Finset.range n, (n - j) • bracket f j

/-- Telescópio: o bracket soma ao incremento da primeira diferença. -/
theorem sum_range_bracket (f : ℕ → E) (n : ℕ) :
    ∑ j ∈ Finset.range n, bracket f j = fdiff f n - fdiff f 0 := by
  simp only [bracket_eq_fdiff_sub]
  exact Finset.sum_range_sub (fdiff f) n

/-- Recorrência de um passo da integral de Green. -/
theorem greenSum_succ (f : ℕ → E) (n : ℕ) :
    greenSum f (n + 1) = greenSum f n + (fdiff f (n + 1) - fdiff f 0) := by
  have e1 : greenSum f (n + 1)
      = (∑ j ∈ Finset.range n, ((n - j) • bracket f j + bracket f j))
        + bracket f n := by
    unfold greenSum
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      have hjn : j ≤ n := le_of_lt (Finset.mem_range.mp hj)
      have hsub : n + 1 - j = (n - j) + 1 := by omega
      rw [hsub, succ_nsmul]
    · have hlast : n + 1 - n = 1 := by omega
      rw [hlast, one_smul]
  have hB : (∑ j ∈ Finset.range n, bracket f j) + bracket f n
      = fdiff f (n + 1) - fdiff f 0 := by
    rw [← Finset.sum_range_succ]
    exact sum_range_bracket f (n + 1)
  rw [e1, Finset.sum_add_distrib]
  show (greenSum f n + ∑ j ∈ Finset.range n, bracket f j) + bracket f n
      = greenSum f n + (fdiff f (n + 1) - fdiff f 0)
  rw [← hB]; abel

/-- **Teorema Fundamental da Válvula Discreta.**
Todo estado é o retorno afim do seu traço mais a integral de Green da sua
curvatura: `f(n+1) = f(0) + (n+1)•(f 1 - f 0) + (G (B f)) n`. Nenhum dos dois
registros — traço de bordo (valor+inclinação) ou bracket (curvatura) — contém
o estado isoladamente; juntos, o reconstroem sem perda. -/
theorem discrete_valve (f : ℕ → E) (n : ℕ) :
    f (n + 1) = f 0 + (n + 1) • (f 1 - f 0) + greenSum f n := by
  induction n with
  | zero =>
    simp only [Nat.zero_add, greenSum, Finset.range_zero, Finset.sum_empty,
      add_zero, one_smul]
    abel
  | succ n ih =>
    have hstep : f (n + 1 + 1) = f (n + 1) + fdiff f (n + 1) := by
      simp only [fdiff]; abel
    have hf0 : fdiff f 0 = f 1 - f 0 := rfl
    have hsmul : (n + 1 + 1) • (f 1 - f 0) = (n + 1) • (f 1 - f 0) + (f 1 - f 0) := by
      rw [succ_nsmul]
    rw [hstep, ih, greenSum_succ, hf0, hsmul]
    abel

/-! ## Identidades componentes da válvula -/

/-- `B ∘ G = I` (forma deslocada): a segunda diferença da integral de Green
devolve o bracket original. -/
theorem bracket_greenSum (f : ℕ → E) (n : ℕ) :
    greenSum f (n + 1 + 1) - 2 • greenSum f (n + 1) + greenSum f n
      = bracket f (n + 1) := by
  rw [greenSum_succ f (n + 1), greenSum_succ f n, bracket_eq_fdiff_sub f (n + 1),
    two_smul]
  abel

/-- O canal de Green começa vazio: `G (B f)` em `0` é nulo, logo o traço de `f`
(valor + inclinação) vive inteiramente no canal afim de retorno `R (Tr f)`. -/
theorem greenSum_zero (f : ℕ → E) : greenSum f 0 = 0 := by
  simp [greenSum]

/-! ## Lei de conservação: kernel do bracket -/

/-- **Kernel do bracket = estados afins.** Curvatura-zero equivale a puro bordo:
`f` tem bracket identicamente nulo se e só se é a forma afim do seu traço,
`f n = f 0 + n • (f 1 - f 0)`. É o ponto fixo trivial da válvula aditiva
(sem cauda de Green), análogo ao canal nulo ⟺ massa trivial do lado
multiplicativo. -/
theorem bracket_eq_zero_iff_affine (f : ℕ → E) :
    (∀ j, bracket f j = 0) ↔ ∀ n, f n = f 0 + n • (f 1 - f 0) := by
  constructor
  · intro hbr n
    cases n with
    | zero => simp
    | succ m =>
      have hg : greenSum f m = 0 := by
        unfold greenSum
        apply Finset.sum_eq_zero
        intro j _
        rw [hbr j, smul_zero]
      rw [discrete_valve f m, hg, add_zero]
  · intro haff j
    rw [bracket_eq_fdiff_sub]
    have hf : ∀ k, fdiff f k = f 1 - f 0 := by
      intro k
      unfold fdiff
      rw [haff (k + 1), haff k, succ_nsmul]
      abel
    rw [hf (j + 1), hf j, sub_self]

/-! ## Linearidade das válvulas -/

/-- O bracket é aditivo. -/
theorem bracket_add (f g : ℕ → E) (j : ℕ) :
    bracket (f + g) j = bracket f j + bracket g j := by
  simp only [bracket, Pi.add_apply]
  abel

/-- A integral de Green é aditiva: `greenSum` é linear em `f`, o análogo aditivo
do homomorfismo `× → +` do canal multiplicativo. -/
theorem greenSum_add (f g : ℕ → E) (n : ℕ) :
    greenSum (f + g) n = greenSum f n + greenSum g n := by
  unfold greenSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [bracket_add, smul_add]

end CarrySelfAdjointOperator.DiscreteValve
