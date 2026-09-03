import CarrySelfAdjointOperator.ProjectiveValveEquivalence

/-!
# Álgebra da válvula projetiva

A equivalência projetiva identifica uma curvatura formal `D` com a única massa
normalizada `A` que satisfaz

`A' = D * A`,  `A(0) = 1`.

Este arquivo prova que essa identificação respeita as operações naturais:

* soma de curvaturas vira produto de massas;
* zero vira a massa unidade;
* negação vira inversão;
* produto de massas normalizadas vira soma de curvaturas.

Assim a válvula deixa de ser apenas uma equivalência de conjuntos e passa a
exibir sua estrutura exponencial intrínseca.
-/

namespace CarrySelfAdjointOperator.ProjectiveValve

open PowerSeries
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

/-- Curvatura nula produz a massa unidade. -/
@[simp] theorem projectiveValveMass_zero :
    projectiveValveMass (0 : PowerSeries K) = 1 := by
  symm
  exact projectiveValveMass_unique (0 : PowerSeries K) 1
    (by simp) (by simp)

/-- Soma de curvaturas vira produto das massas canônicas. -/
theorem projectiveValveMass_add (D E : PowerSeries K) :
    projectiveValveMass (D + E) =
      projectiveValveMass D * projectiveValveMass E := by
  symm
  apply projectiveValveMass_unique (D + E)
    (projectiveValveMass D * projectiveValveMass E)
  · simp
  · have hD := derivative_projectiveValveMass D
    have hE := derivative_projectiveValveMass E
    change (projectiveValveMass D).derivativeFun =
      D * projectiveValveMass D at hD
    change (projectiveValveMass E).derivativeFun =
      E * projectiveValveMass E at hE
    change (projectiveValveMass D * projectiveValveMass E).derivativeFun =
      (D + E) * (projectiveValveMass D * projectiveValveMass E)
    rw [PowerSeries.derivativeFun_mul, hD, hE]
    simp only [smul_eq_mul]
    ring

/-- Uma soma finita de curvaturas integra para o produto finito das massas. -/
theorem projectiveValveMass_sum
    {ι : Type*} (s : Finset ι) (D : ι → PowerSeries K) :
    projectiveValveMass (∑ i in s, D i) =
      ∏ i in s, projectiveValveMass (D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp [hi, projectiveValveMass_add, ih]

/-- Negar a curvatura inverte a massa normalizada. -/
@[simp] theorem projectiveValveMass_neg (D : PowerSeries K) :
    projectiveValveMass (-D) = (projectiveValveMass D)⁻¹ := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one
    (show constantCoeff (projectiveValveMass D) ≠ 0 by simp)).2
  rw [← projectiveValveMass_add]
  simp

/-- Diferença de curvaturas vira quociente multiplicativo de massas. -/
theorem projectiveValveMass_sub (D E : PowerSeries K) :
    projectiveValveMass (D - E) =
      projectiveValveMass D * (projectiveValveMass E)⁻¹ := by
  rw [sub_eq_add_neg, projectiveValveMass_add, projectiveValveMass_neg]

/-- A massa unidade tem curvatura nula. -/
@[simp] theorem projectiveValveCurvature_one :
    projectiveValveCurvature (1 : PowerSeries K) = 0 := by
  simp [projectiveValveCurvature]

/-- Produto de massas normalizadas soma suas curvaturas. -/
theorem projectiveValveCurvature_mul
    (A B : PowerSeries K)
    (hA0 : constantCoeff A = 1)
    (hB0 : constantCoeff B = 1) :
    projectiveValveCurvature (A * B) =
      projectiveValveCurvature A + projectiveValveCurvature B := by
  calc
    projectiveValveCurvature (A * B) =
        projectiveValveCurvature
          (projectiveValveMass (projectiveValveCurvature A) *
            projectiveValveMass (projectiveValveCurvature B)) := by
      rw [projectiveValveMass_projectiveValveCurvature A hA0,
        projectiveValveMass_projectiveValveCurvature B hB0]
    _ = projectiveValveCurvature
        (projectiveValveMass
          (projectiveValveCurvature A + projectiveValveCurvature B)) := by
      rw [projectiveValveMass_add]
    _ = projectiveValveCurvature A + projectiveValveCurvature B := by
      rw [projectiveValveCurvature_projectiveValveMass]

/-- Inverter uma massa normalizada nega sua curvatura. -/
@[simp] theorem projectiveValveCurvature_inv
    (A : PowerSeries K)
    (hA0 : constantCoeff A = 1) :
    projectiveValveCurvature A⁻¹ = -projectiveValveCurvature A := by
  calc
    projectiveValveCurvature A⁻¹ =
        projectiveValveCurvature
          (projectiveValveMass (projectiveValveCurvature A)⁻¹) := by
      rw [projectiveValveMass_projectiveValveCurvature A hA0]
    _ = projectiveValveCurvature
        (projectiveValveMass (-projectiveValveCurvature A)) := by
      rw [projectiveValveMass_neg]
    _ = -projectiveValveCurvature A := by
      rw [projectiveValveCurvature_projectiveValveMass]

/-- Quociente de massas normalizadas subtrai suas curvaturas. -/
theorem projectiveValveCurvature_div
    (A B : PowerSeries K)
    (hA0 : constantCoeff A = 1)
    (hB0 : constantCoeff B = 1) :
    projectiveValveCurvature (A * B⁻¹) =
      projectiveValveCurvature A - projectiveValveCurvature B := by
  have hBinv0 : constantCoeff B⁻¹ = 1 := by
    simp [hB0]
  rw [projectiveValveCurvature_mul A B⁻¹ hA0 hBinv0,
    projectiveValveCurvature_inv B hB0, sub_eq_add_neg]

end CarrySelfAdjointOperator.ProjectiveValve
