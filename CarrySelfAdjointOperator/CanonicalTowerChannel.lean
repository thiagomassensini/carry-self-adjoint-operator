import CarrySelfAdjointOperator.MultiplicativeValve

/-!
# Canal canônico da válvula multiplicativa

A relação `IsTowerChannel a b` já caracteriza o canal de uma massa normalizada,
mas uma geometria canônica pede mais do que unicidade condicional: pede o mapa
explícito `a ↦ b`.

Este arquivo resolve triangularmente

`∑_{i=0}^n b i * a (n-i) = n * a n`

sem divisão, desde que `a 0 = 1`. Assim toda massa normalizada possui exatamente
um canal. Sobre um corpo de característica zero, essa diferenciação canônica é
inversa à integração `towerMass`, fechando os dois percursos da válvula.
-/

namespace CarrySelfAdjointOperator.MultiplicativeValve

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Canal canônico de uma massa de torre. O novo coeficiente é obtido subtraindo
da graduação `n * a n` toda a contribuição dos coeficientes anteriores. -/
noncomputable def canonicalTowerChannel (a : ℕ → R) : ℕ → R :=
  Nat.lt_wfRel.wf.fix fun n previous =>
    (n : R) * a n -
      ∑ i : Fin n, previous i i.isLt * a (n - i)

/-- Equação de desdobramento da reconstrução triangular do canal. -/
theorem canonicalTowerChannel_eq (a : ℕ → R) (n : ℕ) :
    canonicalTowerChannel a n =
      (n : R) * a n -
        ∑ i ∈ Finset.range n,
          canonicalTowerChannel a i * a (n - i) := by
  rw [canonicalTowerChannel, WellFounded.fix_eq]
  refine congrArg (fun s : R => (n : R) * a n - s) ?_
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dif_pos (Finset.mem_range.mp hi)]

/-- O termo constante de todo canal canônico é zero. -/
@[simp] theorem canonicalTowerChannel_zero (a : ℕ → R) :
    canonicalTowerChannel a 0 = 0 := by
  rw [canonicalTowerChannel_eq]
  simp

/-- Toda massa normalizada possui o canal construído triangularmente. -/
theorem canonicalTowerChannel_isTowerChannel
    (a : ℕ → R) (ha : a 0 = 1) :
    IsTowerChannel a (canonicalTowerChannel a) := by
  intro n
  rw [Finset.sum_range_succ, Nat.sub_self, ha, mul_one,
    canonicalTowerChannel_eq a n]
  ring

/-- Qualquer canal de uma massa normalizada coincide com o canal canônico. -/
theorem canonicalTowerChannel_eq_of_isTowerChannel
    (a b : ℕ → R) (ha : a 0 = 1)
    (hb : IsTowerChannel a b) :
    canonicalTowerChannel a = b :=
  tower_channel_unique a (canonicalTowerChannel a) b ha
    (canonicalTowerChannel_isTowerChannel a ha) hb

/-- Teorema fundamental na direção massa para canal: toda massa normalizada
possui exatamente um canal. -/
theorem existsUnique_towerChannel
    (a : ℕ → R) (ha : a 0 = 1) :
    ∃! b : ℕ → R, IsTowerChannel a b := by
  refine ⟨canonicalTowerChannel a,
    canonicalTowerChannel_isTowerChannel a ha, ?_⟩
  intro b hb
  exact (canonicalTowerChannel_eq_of_isTowerChannel a b ha hb).symm

section CharacteristicZero

variable {K : Type*} [Field K] [CharZero K]

/-- Integrar o canal canônico de uma massa recupera a massa. -/
theorem towerMass_canonicalTowerChannel
    (a : ℕ → K) (ha : a 0 = 1) :
    towerMass (canonicalTowerChannel a) = a :=
  towerMass_eq_of_isTowerChannel a (canonicalTowerChannel a) ha
    (canonicalTowerChannel_isTowerChannel a ha)

/-- Extrair o canal da massa integrada recupera o canal original. -/
theorem canonicalTowerChannel_towerMass
    (b : ℕ → K) (hb : b 0 = 0) :
    canonicalTowerChannel (towerMass b) = b :=
  canonicalTowerChannel_eq_of_isTowerChannel (towerMass b) b
    (towerMass_zero b) (isTowerChannel_towerMass b hb)

/-- Toda massa normalizada é a exponencial formal da integral logarítmica de
seu canal canônico. -/
theorem mk_eq_expSeries_logIntegral_canonicalTowerChannel
    (a : ℕ → K) (ha : a 0 = 1) :
    PowerSeries.mk a =
      expSeries (logIntegral (canonicalTowerChannel a)) := by
  calc
    PowerSeries.mk a =
        PowerSeries.mk (towerMass (canonicalTowerChannel a)) :=
      congrArg (fun f : ℕ → K => PowerSeries.mk f)
        (towerMass_canonicalTowerChannel a ha).symm
    _ = expSeries (logIntegral (canonicalTowerChannel a)) :=
      mk_towerMass_eq_expSeries (canonicalTowerChannel a)
        (canonicalTowerChannel_zero a)

end CharacteristicZero

end CarrySelfAdjointOperator.MultiplicativeValve
