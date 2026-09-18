import CarrySelfAdjointOperator.FiveFieldDecoratedLeveltLocal

/-!
# Exact two-jump fusion cross block

The four coefficients are computed from the actual monodromy matrices and
their amplitude/decoration derivatives, following
`FUSION_GOLDMAN_CROSS_TERM_E_OBSTRUCAO_PREREDUCAO.md`.
This is the cross block before global reduction, with the overall factor
`κ` omitted as in the accompanying symbolic script. No global symplectic
reduction or physical Jacobian identity is asserted.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

open scoped Matrix.Norms.Elementwise

def decoratedMonodromy (a η : ℂ) : TwoByTwo :=
  1 + a • decoratedNilpotent η

/-- Polynomial inverse, justified on both sides below. -/
def decoratedMonodromyInverse (a η : ℂ) : TwoByTwo :=
  1 - a • decoratedNilpotent η

theorem decoratedMonodromy_mul_inverse (a η : ℂ) :
    decoratedMonodromy a η * decoratedMonodromyInverse a η = 1 ∧
      decoratedMonodromyInverse a η * decoratedMonodromy a η = 1 := by
  have h : (a • decoratedNilpotent η) * (a • decoratedNilpotent η) = 0 := by
    simp [decoratedNilpotent_square_zero]
  constructor <;> simp only [decoratedMonodromy, decoratedMonodromyInverse,
    mul_sub, sub_mul, mul_add, add_mul, one_mul, mul_one, h] <;> abel

theorem decoratedMonodromy_hasDerivAt_amplitude (a η : ℂ) :
    HasDerivAt (fun b => decoratedMonodromy b η) (decoratedNilpotent η) a := by
  convert! (hasDerivAt_const a (1 : TwoByTwo)).add
    (decoratedLeveltResidue_hasDerivAt_amplitude 1 a η) using 1 <;>
    simp [decoratedMonodromy, decoratedLeveltResidue, Pi.add_def]

theorem decoratedMonodromy_hasDerivAt_decoration (a η : ℂ) :
    HasDerivAt (decoratedMonodromy a) (a • decoratedNilpotentTangent η) η := by
  convert! (hasDerivAt_const η (1 : TwoByTwo)).add
    (decoratedLeveltResidue_hasDerivAt_decoration 1 a η) using 1
  · funext e
    simp [decoratedMonodromy, decoratedLeveltResidue]
  · simp

/-- Index 0 is amplitude, index 1 is fixed-line decoration. -/
def decoratedMonodromyTangents (a η : ℂ) : Fin 2 → TwoByTwo :=
  ![decoratedNilpotent η, a • decoratedNilpotentTangent η]

/-- Cross coefficients of `(1/2) trace (M1⁻¹ dM1 ∧ dM2 M2⁻¹)`.
Rows belong to the first jump, columns to the second. -/
def decoratedFusionBlock (a1 a2 η1 η2 : ℂ) : TwoByTwo :=
  Matrix.of fun i j =>
    Matrix.trace
      ((decoratedMonodromyInverse a1 η1 * decoratedMonodromyTangents a1 η1 i) *
        (decoratedMonodromyTangents a2 η2 j * decoratedMonodromyInverse a2 η2)) / 2

theorem decoratedFusionBlock_eq (a1 a2 η1 η2 : ℂ) :
    decoratedFusionBlock a1 a2 η1 η2 =
      !![-(η1 - η2)^2 / 2,
          -a2 * (η1 - η2) * (a2 * (η1 - η2) - 2) / 2;
        a1 * (η1 - η2) * (a1 * (η1 - η2) - 2) / 2,
          a1 * a2 / 2 *
            (a1 * a2 * (η1 - η2)^2 - 2 * (a1 + a2) * (η1 - η2) + 2)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [decoratedFusionBlock, decoratedMonodromyInverse, decoratedMonodromyTangents,
      decoratedNilpotent, decoratedNilpotentTangent, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem decoratedMonodromy_product_trace (a1 a2 η1 η2 : ℂ) :
    Matrix.trace (decoratedMonodromy a1 η1 * decoratedMonodromy a2 η2) =
      2 - a1 * a2 * (η1 - η2)^2 := by
  simp [decoratedMonodromy, decoratedNilpotent, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem decoratedMonodromy_commutator_upper (a1 a2 η1 η2 : ℂ) :
    matrixCommutator (decoratedMonodromy a1 η1) (decoratedMonodromy a2 η2) 0 1 =
      -2 * a1 * a2 * (η1 - η2) := by
  simp [matrixCommutator, decoratedMonodromy, decoratedNilpotent,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- At a common fixed line the transverse coefficient survives. -/
theorem decoratedFusionBlock_same_line (a1 a2 η : ℂ) :
    decoratedFusionBlock a1 a2 η η = !![0, 0; 0, a1 * a2] := by
  rw [decoratedFusionBlock_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Exact rational specialization, not a numerical fit. -/
theorem decoratedFusionBlock_physical :
    decoratedFusionBlock (-8 / 33) (-3 / 11) 0 0 =
      !![0, 0; 0, (8 / 121 : ℂ)] := by
  rw [decoratedFusionBlock_same_line]
  norm_num

end

end NativeCarryFiveFieldCapstone
