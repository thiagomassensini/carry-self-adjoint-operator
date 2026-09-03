import CarrySelfAdjointOperator.ProjectiveValveFundamentalTheorem

/-!
# Equivalência entre curvaturas projetivas e massas normalizadas

O Teorema Fundamental da Válvula Projetiva já prova que toda curvatura formal
`D` determina uma única massa normalizada `A` satisfazendo

`A' = D * A`,  `A(0) = 1`.

A geometria pede agora a direção inversa explícita. Para uma massa normalizada,
a curvatura é sua derivada logarítmica formal

`D = A' * A⁻¹`.

Este arquivo prova os dois percursos e empacota a válvula como uma equivalência
canônica entre todas as curvaturas formais e as massas de termo constante `1`.
-/

namespace CarrySelfAdjointOperator.ProjectiveValve

open PowerSeries

variable {K : Type*} [Field K]

/-- Curvatura projetiva extraída de uma massa formal: `D = A'/A`. -/
noncomputable def projectiveValveCurvature
    (A : PowerSeries K) : PowerSeries K :=
  (d⁄dX K A) * A⁻¹

/-- Para uma massa normalizada, a curvatura extraída recompõe sua derivada:
`projectiveValveCurvature A * A = A'`. -/
theorem projectiveValveCurvature_mul_self
    (A : PowerSeries K)
    (hA0 : constantCoeff A = 1) :
    projectiveValveCurvature A * A = d⁄dX K A := by
  have hA0ne : constantCoeff A ≠ 0 := by
    rw [hA0]
    exact one_ne_zero
  unfold projectiveValveCurvature
  rw [mul_assoc, PowerSeries.inv_mul_cancel A hA0ne, mul_one]

/-- Qualquer solução normalizada de `A' = D*A` possui exatamente a curvatura
`D`. -/
theorem projectiveValveCurvature_eq_of_ode
    (D A : PowerSeries K)
    (hA0 : constantCoeff A = 1)
    (hA : d⁄dX K A = D * A) :
    projectiveValveCurvature A = D := by
  have hA0ne : constantCoeff A ≠ 0 := by
    rw [hA0]
    exact one_ne_zero
  unfold projectiveValveCurvature
  rw [hA, mul_assoc, PowerSeries.mul_inv_cancel A hA0ne, mul_one]

variable [CharZero K]

/-- Extrair a curvatura da massa canônica recupera a curvatura original. -/
@[simp] theorem projectiveValveCurvature_projectiveValveMass
    (D : PowerSeries K) :
    projectiveValveCurvature (projectiveValveMass D) = D := by
  exact projectiveValveCurvature_eq_of_ode D (projectiveValveMass D)
    (projectiveValveMass_constantCoeff D)
    (derivative_projectiveValveMass D)

/-- Reconstruir a massa da curvatura extraída recupera toda massa normalizada. -/
@[simp] theorem projectiveValveMass_projectiveValveCurvature
    (A : PowerSeries K)
    (hA0 : constantCoeff A = 1) :
    projectiveValveMass (projectiveValveCurvature A) = A := by
  exact (projectiveValveMass_unique
    (projectiveValveCurvature A) A hA0
    (projectiveValveCurvature_mul_self A hA0).symm).symm

/-- Espaço das massas formais normalizadas da válvula projetiva. -/
def NormalizedProjectiveMass (K : Type*) [Field K] :=
  {A : PowerSeries K // constantCoeff A = 1}

/-- **Equivalência da válvula projetiva.** Curvaturas formais e massas
normalizadas são coordenadas canonicamente equivalentes:

`D ↦ projectiveValveMass D`,

`A ↦ A' * A⁻¹`.
-/
noncomputable def projectiveValveEquiv :
    PowerSeries K ≃ NormalizedProjectiveMass K where
  toFun D := ⟨projectiveValveMass D, projectiveValveMass_constantCoeff D⟩
  invFun A := projectiveValveCurvature A.1
  left_inv := by
    intro D
    exact projectiveValveCurvature_projectiveValveMass D
  right_inv := by
    intro A
    apply Subtype.ext
    exact projectiveValveMass_projectiveValveCurvature A.1 A.2

/-- A massa canônica é injetiva como função da curvatura. -/
theorem projectiveValveMass_injective :
    Function.Injective (projectiveValveMass : PowerSeries K → PowerSeries K) := by
  intro D E hDE
  have h := congrArg projectiveValveCurvature hDE
  simpa using h

/-- Toda curvatura formal é a curvatura de uma massa normalizada. -/
theorem projectiveValveCurvature_surjective :
    Function.Surjective
      (fun A : NormalizedProjectiveMass K => projectiveValveCurvature A.1) := by
  intro D
  refine ⟨⟨projectiveValveMass D, projectiveValveMass_constantCoeff D⟩, ?_⟩
  exact projectiveValveCurvature_projectiveValveMass D

end CarrySelfAdjointOperator.ProjectiveValve
