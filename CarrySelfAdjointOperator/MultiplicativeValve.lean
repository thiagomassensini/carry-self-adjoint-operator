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

/-! ## Ponte: canal-sequência ↔ canal-série -/

/-- **Ponte.** As duas faces do canal são o mesmo objeto: a deconvolução de
Dirichlet da sequência (`IsTowerChannel a b`) equivale à log-derivada formal
(`IsLogDerivChannel (mk a) (mk b)`). A recuperação de von Mangoldt (sequência) e
o homomorfismo (série) vivem numa única identidade. -/
theorem isTowerChannel_iff_isLogDerivChannel (a b : ℕ → R) :
    IsTowerChannel a b ↔ IsLogDerivChannel (PowerSeries.mk a) (PowerSeries.mk b) := by
  have hlhs : ∀ n, (PowerSeries.coeff n) (PowerSeries.mk b * PowerSeries.mk a)
      = ∑ i ∈ Finset.range (n + 1), b i * a (n - i) := by
    intro n
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [PowerSeries.coeff_mk]
  have hrhs : ∀ n, (PowerSeries.coeff n)
      (PowerSeries.X * (PowerSeries.mk a).derivativeFun) = (n : R) * a n := by
    intro n
    cases n with
    | zero => simp
    | succ m =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivativeFun,
        PowerSeries.coeff_mk]
      push_cast
      ring
  unfold IsTowerChannel IsLogDerivChannel
  rw [PowerSeries.ext_iff]
  exact forall_congr' fun n => by rw [hlhs, hrhs]

/-! ## Integração: reconstrução canônica da massa a partir do canal -/

section Reconstruction

variable {K : Type*} [Field K] [CharZero K]

/-- Massa de torre reconstruída a partir do canal `b` (a "integração"
multiplicativa): resolve `n · aₙ = Σ_{i≥1} bᵢ · a_{n-i}` com `a₀ = 1`. O fator
`1/n` é a integração que inverte a log-derivada. -/
noncomputable def towerMass (b : ℕ → K) : ℕ → K
  | 0 => 1
  | (n + 1) => (↑(n + 1) : K)⁻¹ *
      ∑ i ∈ (Finset.range (n + 1)).attach, b (i.1 + 1) * towerMass b (n - i.1)
  decreasing_by
    have := Finset.mem_range.mp i.2
    omega

omit [CharZero K] in
@[simp] theorem towerMass_zero (b : ℕ → K) : towerMass b 0 = 1 := by
  rw [towerMass]

/-- **Reconstrução canônica (existência).** A integração `b ↦ towerMass b`
produz uma massa cujo canal é de fato `b`, desde que `b 0 = 0`. É a válvula
multiplicativa na direção da integração, análoga a `discrete_valve`. -/
theorem isTowerChannel_towerMass (b : ℕ → K) (hb : b 0 = 0) :
    IsTowerChannel (towerMass b) b := by
  intro n
  cases n with
  | zero => simp [hb]
  | succ m =>
    have hm : ((m + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    have hrhs : ((m + 1 : ℕ) : K) * towerMass b (m + 1)
        = ∑ i ∈ Finset.range (m + 1), b (i + 1) * towerMass b (m - i) := by
      rw [towerMass, ← mul_assoc, mul_inv_cancel₀ hm, one_mul,
        Finset.sum_attach (Finset.range (m + 1))
          (fun i => b (i + 1) * towerMass b (m - i))]
    rw [hrhs, Finset.sum_range_succ', hb, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.succ_sub_succ]

/-- **Reconstrução canônica (unicidade).** Sobre um corpo de característica `0`,
a massa com `a 0 = 1` e canal `b` é única: o canal determina a massa. É a
integração multiplicativa `b ↦ a` (inversa da log-derivada), análoga a
`discrete_valve` no lado aditivo. -/
theorem towerMass_unique (a a' b : ℕ → K) (ha : a 0 = 1) (ha' : a' 0 = 1)
    (h : IsTowerChannel a b) (h' : IsTowerChannel a' b) : a = a' := by
  have hb0 : b 0 = 0 := by
    have h0 := h 0
    simp only [zero_add, Finset.sum_range_one, Nat.sub_zero, ha, mul_one,
      Nat.cast_zero] at h0
    exact h0
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · rw [ha, ha']
    · have hn : ((m + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      have ea := h (m + 1)
      have ea' := h' (m + 1)
      rw [Finset.sum_range_succ'] at ea ea'
      simp only [hb0, zero_mul, add_zero, Nat.sub_zero] at ea ea'
      have hsum : ∑ i ∈ Finset.range (m + 1), b (i + 1) * a (m + 1 - (i + 1))
          = ∑ i ∈ Finset.range (m + 1), b (i + 1) * a' (m + 1 - (i + 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hlt : m + 1 - (i + 1) < m + 1 := by
          have := Finset.mem_range.mp hi; omega
        rw [ih _ hlt]
      rw [hsum] at ea
      exact mul_left_cancel₀ hn (ea.symm.trans ea')

end Reconstruction

end CarrySelfAdjointOperator.MultiplicativeValve
