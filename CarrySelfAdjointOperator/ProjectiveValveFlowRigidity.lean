import CarrySelfAdjointOperator.ProjectiveValveFlow

/-!
# Rigidez do fluxo da válvula projetiva

Fixada uma curvatura formal `D`, o fluxo projetivo

`Φ_D(t) = projectiveValveMass (t • D)`

já forma um subgrupo a um parâmetro. Este arquivo fecha as propriedades
geométricas imediatamente seguintes:

* escalar o gerador apenas reparametriza o fluxo;
* duas posições do fluxo coincidem exatamente quando as curvaturas escaladas
  coincidem;
* o núcleo é dado por `t • D = 0`;
* para gerador não nulo, o fluxo é fiel e injetivo;
* tempos naturais correspondem a potências da massa em tempo um.

Tudo é algébrico e formal. Nenhuma topologia ou aplicação externa entra nos
enunciados.
-/

namespace CarrySelfAdjointOperator.ProjectiveValve

open PowerSeries

variable {K : Type*} [Field K] [CharZero K]

/-- Escalar o gerador equivale a reparametrizar o tempo. -/
theorem projectiveValveFlow_reparameterize
    (D : PowerSeries K) (r t : K) :
    projectiveValveFlow (r • D) t =
      projectiveValveFlow D (t * r) := by
  apply Subtype.ext
  change projectiveValveMass (t • (r • D)) =
    projectiveValveMass ((t * r) • D)
  rw [smul_smul]

/-- A bilinearidade escalar torna simétrica a troca entre gerador e tempo. -/
theorem projectiveValveFlow_scalar_swap
    (D : PowerSeries K) (s t : K) :
    projectiveValveFlow (s • D) t =
      projectiveValveFlow (t • D) s := by
  calc
    projectiveValveFlow (s • D) t =
        projectiveValveFlow D (t * s) :=
      projectiveValveFlow_reparameterize D s t
    _ = projectiveValveFlow D (s * t) := by rw [mul_comm]
    _ = projectiveValveFlow (t • D) s :=
      (projectiveValveFlow_reparameterize D t s).symm

/-- O gerador nulo produz o fluxo constantemente igual à massa unidade. -/
@[simp] theorem projectiveValveFlow_zero_generator
    (t : K) :
    projectiveValveFlow (0 : PowerSeries K) t = 1 := by
  apply Subtype.ext
  change projectiveValveMass (t • (0 : PowerSeries K)) =
    (1 : PowerSeries K)
  simp

/-- Duas posições do fluxo coincidem exatamente quando suas curvaturas
escaladas coincidem. -/
theorem projectiveValveFlow_eq_iff
    (D : PowerSeries K) (s t : K) :
    projectiveValveFlow D s = projectiveValveFlow D t ↔
      s • D = t • D := by
  constructor
  · intro h
    apply projectiveValveMass_injective
    have hval := congrArg
      (fun A : NormalizedProjectiveMass K => A.1) h
    change projectiveValveMass (s • D) =
      projectiveValveMass (t • D) at hval
    exact hval
  · intro h
    apply Subtype.ext
    change projectiveValveMass (s • D) =
      projectiveValveMass (t • D)
    exact congrArg (fun E : PowerSeries K => projectiveValveMass E) h

/-- Forma por diferença da classificação exata das colisões do fluxo. -/
theorem projectiveValveFlow_eq_iff_sub_smul_eq_zero
    (D : PowerSeries K) (s t : K) :
    projectiveValveFlow D s = projectiveValveFlow D t ↔
      (s - t) • D = 0 := by
  rw [projectiveValveFlow_eq_iff D s t, sub_smul, sub_eq_zero]

/-- O núcleo do fluxo é exatamente o anulador escalar do gerador. -/
theorem projectiveValveFlow_eq_one_iff
    (D : PowerSeries K) (t : K) :
    projectiveValveFlow D t = 1 ↔ t • D = 0 := by
  calc
    projectiveValveFlow D t = 1 ↔
        projectiveValveFlow D t = projectiveValveFlow D 0 := by
      rw [projectiveValveFlow_zero]
    _ ↔ t • D = (0 : K) • D :=
      projectiveValveFlow_eq_iff D t 0
    _ ↔ t • D = 0 := by simp

omit [CharZero K] in
/-- Sobre um corpo, um escalar que anula uma série não nula é zero. -/
private theorem scalar_eq_zero_of_smul_series_eq_zero
    (D : PowerSeries K) (hD : D ≠ 0) {t : K}
    (htD : t • D = 0) :
    t = 0 := by
  by_contra ht
  apply hD
  calc
    D = 1 • D := by simp
    _ = (t⁻¹ * t) • D := by simp [inv_mul_cancel₀ ht]
    _ = t⁻¹ • (t • D) := by rw [smul_smul]
    _ = 0 := by rw [htD, smul_zero]

/-- Para gerador não nulo, somente o tempo zero produz a massa unidade. -/
theorem projectiveValveFlow_eq_one_iff_of_ne
    (D : PowerSeries K) (hD : D ≠ 0) (t : K) :
    projectiveValveFlow D t = 1 ↔ t = 0 := by
  constructor
  · intro h
    exact scalar_eq_zero_of_smul_series_eq_zero D hD
      ((projectiveValveFlow_eq_one_iff D t).mp h)
  · intro ht
    subst t
    exact projectiveValveFlow_zero D

/-- Um gerador não nulo produz um fluxo fiel. -/
theorem projectiveValveFlow_injective_of_ne
    (D : PowerSeries K) (hD : D ≠ 0) :
    Function.Injective (projectiveValveFlow D) := by
  intro s t hst
  have hsmul : s • D = t • D :=
    (projectiveValveFlow_eq_iff D s t).mp hst
  have hzero : (s - t) • D = 0 := by
    rw [sub_smul, hsmul, sub_self]
  exact sub_eq_zero.mp
    (scalar_eq_zero_of_smul_series_eq_zero D hD hzero)

/-- O fluxo é injetivo exatamente quando seu gerador é não nulo. -/
theorem projectiveValveFlow_injective_iff
    (D : PowerSeries K) :
    Function.Injective (projectiveValveFlow D) ↔ D ≠ 0 := by
  constructor
  · intro hinj hD
    have h01 : (0 : K) = 1 := hinj (by
      apply Subtype.ext
      simp [projectiveValveFlow, hD])
    exact zero_ne_one h01
  · exact projectiveValveFlow_injective_of_ne D

/-- Tempos naturais são potências da massa no tempo um. -/
theorem projectiveValveFlow_natCast
    (D : PowerSeries K) (n : ℕ) :
    projectiveValveFlow D (n : K) =
      (projectiveValveFlow D 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, projectiveValveFlow_add, ih, pow_succ]

end CarrySelfAdjointOperator.ProjectiveValve
