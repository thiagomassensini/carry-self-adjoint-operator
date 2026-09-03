import Mathlib

/-!
# Válvula Multiplicativa (núcleo cumulante da teoria de defeitos C2)

Irmã multiplicativa da Válvula Discreta. Onde a válvula aditiva reconstrói um
estado a partir do traço de bordo mais a integral de Green da curvatura (segunda
diferença), aqui a torre de uma base prima é **deconvolvida por Dirichlet**:

`(b ⋆ a)(n) = n · a n`,   com `a 0 = 1`,

produzindo o canal geométrico `b` da massa local `a k = a(p^k)`. Em série formal
isto é `B = E log A` com `A(x) = Σ a k · x^k`: os coeficientes `b k = k · K_k`
são a log-derivada `x A'/A`, e `b(p^k) = K_k · log(p^k)` (o traço vestido
`Ψ = A·B = E·A`, regular).

Dois fatos incondicionais, álgebra finita pura sobre um `CommRing`:

* o canal é **único** dado `a 0 = 1` — a deconvolução é uma válvula exata;
* para a massa de Mellin/Euler `a k = c^k` (`c = p^{-ε}`), o canal é a própria
  massa, `b k = c^k` para `k ≥ 1` — a **recuperação de von Mangoldt**
  `b_ε(p^k) = Λ(p^k) · a_ε(p^k)`, pois `Λ(p^k) = log p` e `c^k = p^{-kε}`.

Sem análise, sem zeta, sem RH.
-/

namespace CarrySelfAdjointOperator.MultiplicativeValve

variable {R : Type*} [CommRing R]

/-- `b` é o canal geométrico (deconvolução de Dirichlet) da massa de torre `a`:
a convolução de Cauchy `b ⋆ a` na posição `n` recupera a graduação `n · a n`. -/
def IsTowerChannel (a b : ℕ → R) : Prop :=
  ∀ n, ∑ i ∈ Finset.range (n + 1), b i * a (n - i) = (n : R) * a n

/-- **Unicidade do canal.** Com `a 0 = 1`, a deconvolução de torre é uma válvula
exata: existe no máximo um canal geométrico. -/
theorem tower_channel_unique (a b₁ b₂ : ℕ → R) (ha : a 0 = 1)
    (h₁ : IsTowerChannel a b₁) (h₂ : IsTowerChannel a b₂) : b₁ = b₂ := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hdist : ∑ i ∈ Finset.range (n + 1), (b₁ i - b₂ i) * a (n - i)
        = (∑ i ∈ Finset.range (n + 1), b₁ i * a (n - i))
          - ∑ i ∈ Finset.range (n + 1), b₂ i * a (n - i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => sub_mul (b₁ i) (b₂ i) (a (n - i))
    have hsum : ∑ i ∈ Finset.range (n + 1), (b₁ i - b₂ i) * a (n - i) = 0 := by
      rw [hdist, h₁ n, h₂ n, sub_self]
    rw [Finset.sum_range_succ] at hsum
    have hzero : ∑ i ∈ Finset.range n, (b₁ i - b₂ i) * a (n - i) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [ih i (Finset.mem_range.mp hi), sub_self, zero_mul]
    rw [hzero, zero_add, Nat.sub_self, ha, mul_one, sub_eq_zero] at hsum
    exact hsum

/-- **Recuperação de von Mangoldt.** A massa de Mellin/Euler `a k = c^k` tem por
canal geométrico a própria massa (`b k = c^k` para `k ≥ 1`, `b 0 = 0`).
Restaurando o fator `log p`, isto é `b_ε(p^k) = Λ(p^k) · a_ε(p^k)`. -/
theorem geometric_isTowerChannel (c : R) :
    IsTowerChannel (fun k => c ^ k) (fun k => if k = 0 then 0 else c ^ k) := by
  intro n
  show ∑ i ∈ Finset.range (n + 1), (if i = 0 then (0 : R) else c ^ i) * c ^ (n - i)
      = (n : R) * c ^ n
  have key : ∀ i ∈ Finset.range (n + 1),
      (if i = 0 then (0 : R) else c ^ i) * c ^ (n - i)
        = if i = 0 then (0 : R) else c ^ n := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0; simp
    · rw [if_neg hipos.ne', if_neg hipos.ne', ← pow_add]
      have hle : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      congr 1
      omega
  rw [Finset.sum_congr rfl key, Finset.sum_range_succ']
  simp

/-! ## Aditividade de canais: a completação `F = A · G` -/

/-- Log-derivada de torre em série formal: `B · A = X · A'`, equivalente a
`B = X·A'/A = 𝓔 log A` onde `A` é unidade. Versão em série formal do canal
cumulante `IsTowerChannel`. -/
def IsLogDerivChannel (A B : PowerSeries R) : Prop :=
  B * A = PowerSeries.X * A.derivativeFun

/-- **Aditividade de canais.** A log-derivada de um produto é a soma das
log-derivadas: `m_{A·G} = m_A + m_G`. É o `F = A·G ⟹ γ_F = γ_A ⊕ γ_G` da
completação — fato puramente algébrico (regra de Leibniz), sem análise. -/
theorem isLogDerivChannel_mul {A₁ A₂ B₁ B₂ : PowerSeries R}
    (h₁ : IsLogDerivChannel A₁ B₁) (h₂ : IsLogDerivChannel A₂ B₂) :
    IsLogDerivChannel (A₁ * A₂) (B₁ + B₂) := by
  unfold IsLogDerivChannel at h₁ h₂ ⊢
  rw [PowerSeries.derivativeFun_mul]
  linear_combination h₁ * A₂ + h₂ * A₁

/-- A massa trivial `A = 1` tem canal nulo: a unidade do monóide multiplicativo
vai para o zero do grupo aditivo de canais. -/
theorem isLogDerivChannel_one : IsLogDerivChannel (1 : PowerSeries R) 0 := by
  have hd : (1 : PowerSeries R).derivativeFun = 0 := by
    ext n
    simp [PowerSeries.coeff_derivativeFun]
  unfold IsLogDerivChannel
  rw [zero_mul, hd, mul_zero]

/-- **A log-derivada é homomorfismo `× → +`.** O canal de uma potência é o
múltiplo do canal: `m_{Aⁿ} = n · m_A`. Repetir uma base `n` vezes escala seu
canal por `n`. -/
theorem isLogDerivChannel_pow {A B : PowerSeries R} (h : IsLogDerivChannel A B) :
    ∀ n : ℕ, IsLogDerivChannel (A ^ n) (n • B)
  | 0 => by simpa using isLogDerivChannel_one
  | n + 1 => by
      rw [pow_succ, succ_nsmul]
      exact isLogDerivChannel_mul (isLogDerivChannel_pow h n) h

/-- **Homomorfismo em produtos finitos.** O canal de um produto de massas é a
soma dos canais: `m_{∏ Aᵢ} = ∑ m_{Aᵢ}`. A "Euler product ↦ soma de canais
locais" da geometria — sem produto de Euler nem zeta como premissa. -/
theorem isLogDerivChannel_prod {ι : Type*} (s : Finset ι) (A B : ι → PowerSeries R)
    (h : ∀ i ∈ s, IsLogDerivChannel (A i) (B i)) :
    IsLogDerivChannel (∏ i ∈ s, A i) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isLogDerivChannel_one
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact isLogDerivChannel_mul (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end CarrySelfAdjointOperator.MultiplicativeValve
