import CarrySelfAdjointOperator.C2LiteralCameraAllOrderJetCrosswalk

open scoped BigOperators

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open CarrySelfAdjointOperator.ProjectiveDepth
open NativeCarrySpectralWeyl.Camera.FiniteBridge

noncomputable section

/-- The real logarithmic weight, viewed as a complex scalar. -/
def c2LegLogWeight (order : ℕ) (x : ℝ) : ℂ :=
  (Real.log x : ℂ) ^ order

/-- The literal C2 leg function `exp (-s log x)`. -/
def c2LegFunction (s : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-s * (Real.log x : ℂ))

/-- The logarithmically weighted value on one leg. -/
def c2LegJetValue (order : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  c2LegLogWeight order x * c2LegFunction s x

/-- The second-difference jet on the two legs and the centre. -/
def c2LegJetBracket (order : ℕ) (s : ℂ) (center : ℝ) : ℂ :=
  c2LegJetValue order s (center - 1) -
    2 * c2LegJetValue order s center +
      c2LegJetValue order s (center + 1)

/-- The part obtained by freezing the Dirichlet factor at the centre. -/
def c2LegCentralPart (order : ℕ) (s : ℂ) (center : ℝ) : ℂ :=
  (c2LegLogWeight order (center - 1) -
      2 * c2LegLogWeight order center +
      c2LegLogWeight order (center + 1)) * c2LegFunction s center

/-- The independent left and right leg increments. -/
def c2LegCompensation (order : ℕ) (s : ℂ) (center : ℝ) : ℂ :=
  c2LegLogWeight order (center - 1) *
      (c2LegFunction s (center - 1) - c2LegFunction s center) +
    c2LegLogWeight order (center + 1) *
      (c2LegFunction s (center + 1) - c2LegFunction s center)

/-- The algebraic identity behind the compensation, with six unconstrained
scalars. -/
theorem c2CenteredSixScalarBracket
    (a b c x y z : ℂ) :
    a * x - 2 * (b * y) + c * z =
      (a - 2 * b + c) * y + a * (x - y) + c * (z - y) := by
  ring

/-- Every logarithmic C2 jet splits into its central part and the two separate
leg increments. -/
theorem c2LegJetBracket_eq_central_add_compensation
    (order : ℕ) (s : ℂ) (center : ℝ) :
    c2LegJetBracket order s center =
      c2LegCentralPart order s center +
        c2LegCompensation order s center := by
  unfold c2LegJetBracket c2LegJetValue c2LegCentralPart
    c2LegCompensation
  simpa only [add_assoc] using
    c2CenteredSixScalarBracket
      (c2LegLogWeight order (center - 1))
      (c2LegLogWeight order center)
      (c2LegLogWeight order (center + 1))
      (c2LegFunction s (center - 1))
      (c2LegFunction s center)
      (c2LegFunction s (center + 1))

@[simp] theorem c2LegFunction_zero_parameter (x : ℝ) :
    c2LegFunction 0 x = 1 := by
  simp [c2LegFunction]

/-- At order zero the central second difference of the constant weight
vanishes. -/
@[simp] theorem c2LegCentralPart_zero_order (s : ℂ) (center : ℝ) :
    c2LegCentralPart 0 s center = 0 := by
  simp only [c2LegCentralPart, c2LegLogWeight, pow_zero]
  ring

/-- The order-zero compensation is exactly the unweighted two-leg bracket. -/
theorem c2LegCompensation_zero_order_eq_bracket (s : ℂ) (center : ℝ) :
    c2LegCompensation 0 s center = c2LegJetBracket 0 s center := by
  have h := c2LegJetBracket_eq_central_add_compensation 0 s center
  simpa using h.symm

/-- At zero spectral parameter both leg increments vanish. -/
@[simp] theorem c2LegCompensation_zero_parameter
    (order : ℕ) (center : ℝ) :
    c2LegCompensation order 0 center = 0 := by
  simp [c2LegCompensation]

/-- On positive inputs, the literal exponential agrees with the repository's
real Dirichlet power. -/
theorem realDirichletPower_eq_c2LegFunction
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    realDirichletPower s x = c2LegFunction s x := by
  rw [realDirichletPower, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [← Complex.ofReal_log hx.le]
  congr 1
  ring

/-- The existing all-order readout is the logarithmic leg value used above. -/
theorem realLogPowerDirichletPower_eq_c2LegJetValue
    (order : ℕ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    realLogPowerDirichletPower order s x = c2LegJetValue order s x := by
  rw [realLogPowerDirichletPower, c2LegJetValue,
    realDirichletPower_eq_c2LegFunction s hx]
  simp [c2LegLogWeight, Complex.ofReal_pow]

/-- A fibre bracket splits into the central part and both leg compensations. -/
theorem c2FiberAllOrderBracket_eq_legParts
    (order m k : ℕ)
    (hcenter : 1 < 2 ^ k * m) :
    c2FiberAllOrderBracket order m k =
      c2LegCentralPart order (1 / 2 : ℂ)
          ((2 ^ k * m : ℕ) : ℝ) +
        c2LegCompensation order (1 / 2 : ℂ)
          ((2 ^ k * m : ℕ) : ℝ) := by
  have hcenter_le : 1 ≤ 2 ^ k * m := hcenter.le
  have hleft : (((2 ^ k * m - 1 : ℕ) : ℝ)) =
      ((2 ^ k * m : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub hcenter_le]
    norm_num
  have hright : (((2 ^ k * m + 1 : ℕ) : ℝ)) =
      ((2 ^ k * m : ℕ) : ℝ) + 1 := by
    norm_num
  unfold c2FiberAllOrderBracket
  rw [hleft, hright]
  have hleft_pos : 0 < 2 ^ k * m - 1 := Nat.sub_pos_of_lt hcenter
  have hleft_real_pos : 0 < (((2 ^ k * m - 1 : ℕ) : ℝ)) := by exact_mod_cast hleft_pos
  have hleft_argument_pos :
      0 < (((2 ^ k * m : ℕ) : ℝ) - 1) := by
    rw [← hleft]
    exact hleft_real_pos
  have hcenter_real_pos : 0 < (((2 ^ k * m : ℕ) : ℝ)) := by positivity
  rw [realLogPowerDirichletPower_eq_c2LegJetValue order (1 / 2 : ℂ)
      hleft_argument_pos,
    realLogPowerDirichletPower_eq_c2LegJetValue order (1 / 2 : ℂ)
      hcenter_real_pos,
    realLogPowerDirichletPower_eq_c2LegJetValue order (1 / 2 : ℂ)
      (by positivity)]
  exact c2LegJetBracket_eq_central_add_compensation order (1 / 2 : ℂ)
    ((2 ^ k * m : ℕ) : ℝ)

/-- The original finite C2 cut remains the explicit seed plus its compensated
fibre sum. -/
theorem c2FiniteCamera_allOrderLogPowerReadout_eq_seed_add_legParts
    (M order : ℕ) :
    evalFormalStencil
        (fun n => realLogPowerDirichletPower order (1 / 2 : ℂ) (n : ℝ))
        (finiteStencil 2 M) =
      evalFormalStencil
          (fun n => realLogPowerDirichletPower order (1 / 2 : ℂ) (n : ℝ))
          (seedStencil 2) +
        ∑ j ∈ Finset.range M,
          (c2LegCentralPart order (1 / 2 : ℂ)
              (((2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j : ℕ) : ℝ)) +
            c2LegCompensation order (1 / 2 : ℂ)
              (((2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j : ℕ) : ℝ))) := by
  rw [c2FiniteCamera_allOrderLogPowerReadout_eq_seed_add_fiberBracketSum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hcenter : 1 < 2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j := by
    rw [← c2AlignedCenter_eq_oddCoreCenter j]
    omega
  simpa using c2FiberAllOrderBracket_eq_legParts order
    (c2AlignedIndexCore j) (c2AlignedIndexDepth j) hcenter

end
end CarrySelfAdjointOperator
