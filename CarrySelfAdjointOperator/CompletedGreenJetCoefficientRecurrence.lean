import CarrySelfAdjointOperator.CompletedGreenMomentJets

/-!
# Exact coefficient recurrence for the completed Green jet kernel

Suppose the normalized odd response has formal coefficients

`m(z) / 2 = sum_n h_n z^(2n+1)`.

Writing the polarized kernel as

`K(z,b) = sum_{p,q} c(p,q) z^q b^p`,

the division-free identity

`(z - b) K(z,b) = (m(z) - m(b)) / 2`

gives an exact coefficient recurrence.  On the interior it transports a
coefficient diagonally to the boundary; on the boundary the odd response
fixes its value.  Hence the whole two-variable kernel is unique.  Its
even/even block is `h_(i+j)`, its odd/odd block is `h_(i+j+1)`, and its mixed
blocks vanish.

This file isolates that all-order algebraic step from the analytic task of
showing that the Taylor-jet Gram coefficients of the concrete completed Green
state satisfy the division-free coefficient equation.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- The `sqrt 2 * F` normalization removes exactly the two scalar factors
carried by the sesquilinear inner product.  This cross-multiplied form avoids
introducing any quotient into the Green identity. -/
theorem normalizedCompletedGreenState_inner_cross_mul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (F : ℂ → ℂ) (state : ℂ → E) (z w : ℂ)
    (hz : F z ≠ 0) (hw : F w ≠ 0) :
    ((2 : ℂ) * (starRingEnd ℂ) (F w) * F z) *
        inner ℂ
          (normalizedCompletedGreenState F state w)
          (normalizedCompletedGreenState F state z) =
      inner ℂ (state w) (state z) := by
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hsqrt_sq : (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hstar : (starRingEnd ℂ) (F w) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hw
  unfold normalizedCompletedGreenState
  rw [inner_smul_left, inner_smul_right]
  simp only [map_inv₀, map_mul, Complex.conj_ofReal]
  field_simp [hz, hstar, hsqrt]
  rw [hsqrt_sq]

/-- A division-free Green representation remains division-free after the
canonical normalization.  The only cost is the explicit scalar factor
`2 * conj(F w) * F z`, which is cancelled algebraically rather than by
dividing the Wronskian. -/
theorem normalizedCompletedGreenState_green_cross_mul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {domain : Set ℂ} {F Psi : ℂ → ℂ} {state : ℂ → E}
    (hgreen : HasDivisionFreeGreenRepresentationOn domain F Psi state)
    {z w : ℂ} (hzDomain : z ∈ domain) (hwDomain : w ∈ domain)
    (hz : F z ≠ 0) (hw : F w ≠ 0) :
    ((2 : ℂ) * (starRingEnd ℂ) (F w) * F z) *
        ((z - (starRingEnd ℂ) w) *
          inner ℂ
            (normalizedCompletedGreenState F state w)
            (normalizedCompletedGreenState F state z)) =
      completedGreenWronskian F Psi z w := by
  calc
    ((2 : ℂ) * (starRingEnd ℂ) (F w) * F z) *
        ((z - (starRingEnd ℂ) w) *
          inner ℂ
            (normalizedCompletedGreenState F state w)
            (normalizedCompletedGreenState F state z)) =
      (z - (starRingEnd ℂ) w) *
        (((2 : ℂ) * (starRingEnd ℂ) (F w) * F z) *
          inner ℂ
            (normalizedCompletedGreenState F state w)
            (normalizedCompletedGreenState F state z)) := by ring
    _ = (z - (starRingEnd ℂ) w) *
        inner ℂ (state w) (state z) := by
      rw [normalizedCompletedGreenState_inner_cross_mul F state z w hz hw]
    _ = completedGreenWronskian F Psi z w :=
      (hgreen z hzDomain w hwDomain).symm

/-- Scalar response naturally seen by the normalized Green state.  For the
canonical companion `Psi = -F'`, this is one half of the negative logarithmic
derivative of `F`. -/
def completedGreenNormalizedResponse
    (F Psi : ℂ → ℂ) (z : ℂ) : ℂ :=
  Psi z / ((2 : ℂ) * F z)

/-- The normalized Green identity is precisely a polarized divided
difference of the scalar response.  This theorem is pointwise on the
nonvanishing neighborhood and follows solely by cancelling the explicit
cross multiplier from the preceding division-free identity. -/
theorem normalizedCompletedGreenState_polarizedResponse
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {domain : Set ℂ} {F Psi : ℂ → ℂ} {state : ℂ → E}
    (hgreen : HasDivisionFreeGreenRepresentationOn domain F Psi state)
    {z w : ℂ} (hzDomain : z ∈ domain) (hwDomain : w ∈ domain)
    (hz : F z ≠ 0) (hw : F w ≠ 0) :
    (z - (starRingEnd ℂ) w) *
        inner ℂ
          (normalizedCompletedGreenState F state w)
          (normalizedCompletedGreenState F state z) =
      completedGreenNormalizedResponse F Psi z -
        (starRingEnd ℂ) (completedGreenNormalizedResponse F Psi w) := by
  have hstar : (starRingEnd ℂ) (F w) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hw
  have hscale :
      (2 : ℂ) * (starRingEnd ℂ) (F w) * F z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hstar) hz
  apply mul_left_cancel₀ hscale
  rw [normalizedCompletedGreenState_green_cross_mul
    hgreen hzDomain hwDomain hz hw]
  unfold completedGreenNormalizedResponse completedGreenWronskian
  simp only [map_div₀, map_mul, map_ofNat]
  field_simp [hz, hw, hstar]

/-- Coefficient on a fixed total-degree diagonal.  Only even total degrees
occur in the quotient of an odd response by `z - b`. -/
def evenMomentDiagonalCoefficient
    (moments : ℕ → ℝ) (n : ℕ) : ℂ :=
  if Even n then (moments (n / 2) : ℂ) else 0

/-- The expected coefficient of `b^p z^q` in the polarized Green kernel. -/
def polarizedGreenMomentCoefficient
    (moments : ℕ → ℝ) (p q : ℕ) : ℂ :=
  evenMomentDiagonalCoefficient moments (p + q)

/-- Coefficients of the normalized odd response
`sum_n h_n z^(2n+1)`. -/
def oddMomentResponseCoefficient
    (moments : ℕ → ℝ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => evenMomentDiagonalCoefficient moments n

@[simp] theorem oddMomentResponseCoefficient_even
    (moments : ℕ → ℝ) (n : ℕ) :
    oddMomentResponseCoefficient moments (2 * n) = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
      rw [show 2 * (n + 1) = Nat.succ (2 * n + 1) by omega]
      change evenMomentDiagonalCoefficient moments (2 * n + 1) = 0
      unfold evenMomentDiagonalCoefficient
      rw [if_neg]
      rintro ⟨k, hk⟩
      omega

@[simp] theorem oddMomentResponseCoefficient_odd
    (moments : ℕ → ℝ) (n : ℕ) :
    oddMomentResponseCoefficient moments (2 * n + 1) =
      (moments n : ℂ) := by
  rw [show 2 * n + 1 = Nat.succ (2 * n) by omega]
  change evenMomentDiagonalCoefficient moments (2 * n) = (moments n : ℂ)
  unfold evenMomentDiagonalCoefficient
  rw [if_pos]
  · congr 2
    omega
  · exact ⟨n, by omega⟩

/-- The original division-free logarithmic-moment recurrence is equivalently
the full convolution coefficient of `q * Phi = -Phi'`.  This is the scalar
source of the odd response after the canonical substitution `u = z^2`; no
spectral or positivity input enters it. -/
theorem logarithmicMoment_fullConvolution
    {phi moments : ℕ → ℝ}
    (hrel : IsLogDerivativeMomentSequence phi moments)
    (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), moments k * phi (n - k) =
      -(((n + 1 : ℕ) : ℝ) * phi (n + 1)) := by
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self]
  have h := hrel n
  linarith

/-- Coefficient form of
`(z - b) K(z,b) = (m(z) - m(b)) / 2`.

The first term is the coefficient contributed by `z * K`, the second by
`b * K`, and the right side is supported on the two coordinate axes. -/
def IsPolarizedGreenCoefficientEquation
    (moments : ℕ → ℝ) (coeff : ℕ → ℕ → ℂ) : Prop :=
  ∀ p q : ℕ,
    (if p = 0 then 0 else coeff (p - 1) q) -
        (if q = 0 then 0 else coeff p (q - 1)) =
      if q = 0 then oddMomentResponseCoefficient moments p
      else if p = 0 then -oddMomentResponseCoefficient moments q
      else 0

/-- The coefficient equation fixes the `q = 0` boundary. -/
theorem polarizedGreenCoefficient_boundary
    {moments : ℕ → ℝ} {coeff : ℕ → ℕ → ℂ}
    (hcoeff : IsPolarizedGreenCoefficientEquation moments coeff)
    (p : ℕ) :
    coeff p 0 = oddMomentResponseCoefficient moments (p + 1) := by
  simpa using hcoeff (p + 1) 0

/-- Away from the axes the coefficient equation is diagonal transport. -/
theorem polarizedGreenCoefficient_transport
    {moments : ℕ → ℝ} {coeff : ℕ → ℕ → ℂ}
    (hcoeff : IsPolarizedGreenCoefficientEquation moments coeff)
    (p q : ℕ) :
    coeff p (q + 1) = coeff (p + 1) q := by
  have h := hcoeff (p + 1) (q + 1)
  simpa [sub_eq_zero] using h

/-- Every coefficient is transported to the unique boundary coefficient on
the same total-degree diagonal. -/
theorem polarizedGreenCoefficient_eq_oddResponse
    {moments : ℕ → ℝ} {coeff : ℕ → ℕ → ℂ}
    (hcoeff : IsPolarizedGreenCoefficientEquation moments coeff)
    (p q : ℕ) :
    coeff p q = oddMomentResponseCoefficient moments (p + q + 1) := by
  induction q generalizing p with
  | zero =>
      simpa using polarizedGreenCoefficient_boundary hcoeff p
  | succ q ih =>
      rw [polarizedGreenCoefficient_transport hcoeff p q, ih (p + 1)]
      congr 2
      omega

/-- The division-free coefficient equation has the unique parity-split
solution expected from the odd moment response. -/
theorem polarizedGreenCoefficient_unique
    {moments : ℕ → ℝ} {coeff : ℕ → ℕ → ℂ}
    (hcoeff : IsPolarizedGreenCoefficientEquation moments coeff)
    (p q : ℕ) :
    coeff p q = polarizedGreenMomentCoefficient moments p q := by
  rw [polarizedGreenCoefficient_eq_oddResponse hcoeff p q]
  change evenMomentDiagonalCoefficient moments (p + q) =
    evenMomentDiagonalCoefficient moments (p + q)
  rfl

@[simp] theorem polarizedGreenMomentCoefficient_even_even
    (moments : ℕ → ℝ) (i j : ℕ) :
    polarizedGreenMomentCoefficient moments (2 * i) (2 * j) =
      (moments (i + j) : ℂ) := by
  unfold polarizedGreenMomentCoefficient evenMomentDiagonalCoefficient
  rw [if_pos]
  · congr 2
    omega
  · exact ⟨i + j, by omega⟩

@[simp] theorem polarizedGreenMomentCoefficient_odd_odd
    (moments : ℕ → ℝ) (i j : ℕ) :
    polarizedGreenMomentCoefficient moments (2 * i + 1) (2 * j + 1) =
      (moments (i + j + 1) : ℂ) := by
  unfold polarizedGreenMomentCoefficient evenMomentDiagonalCoefficient
  rw [if_pos]
  · congr 2
    omega
  · exact ⟨i + j + 1, by omega⟩

@[simp] theorem polarizedGreenMomentCoefficient_even_odd
    (moments : ℕ → ℝ) (i j : ℕ) :
    polarizedGreenMomentCoefficient moments (2 * i) (2 * j + 1) = 0 := by
  unfold polarizedGreenMomentCoefficient evenMomentDiagonalCoefficient
  rw [if_neg]
  rintro ⟨k, hk⟩
  omega

@[simp] theorem polarizedGreenMomentCoefficient_odd_even
    (moments : ℕ → ℝ) (i j : ℕ) :
    polarizedGreenMomentCoefficient moments (2 * i + 1) (2 * j) = 0 := by
  unfold polarizedGreenMomentCoefficient evenMomentDiagonalCoefficient
  rw [if_neg]
  rintro ⟨k, hk⟩
  omega

/-- The coefficient equation for the ordinary Taylor-jet Gram coefficients
is exactly the remaining analytic interface. -/
def HasCompletedGreenJetCoefficientEquation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (moments : ℕ → ℝ) (state : ℂ → E) : Prop :=
  IsPolarizedGreenCoefficientEquation moments fun p q ↦
    inner ℂ (completedGreenTaylorJet state p)
      (completedGreenTaylorJet state q)

/-- Once the Taylor-jet Gram coefficients satisfy the division-free
coefficient equation, diagonal transport supplies the full parity-split Gram
kernel. -/
theorem complexGreenWronskianMomentKernel_of_coefficientEquation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {moments : ℕ → ℝ} {state : ℂ → E}
    (hcoeff : HasCompletedGreenJetCoefficientEquation moments state) :
    IsComplexGreenWronskianMomentKernelGramRepresentation moments
      (completedGreenParityJet state) := by
  intro i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          have h := polarizedGreenCoefficient_unique hcoeff (2 * i) (2 * j)
          simpa [greenWronskianMomentKernel, completedGreenParityJet] using h.symm
      | inr j =>
          have h := polarizedGreenCoefficient_unique hcoeff (2 * i) (2 * j + 1)
          simpa [greenWronskianMomentKernel, completedGreenParityJet] using h.symm
  | inr i =>
      cases j with
      | inl j =>
          have h := polarizedGreenCoefficient_unique hcoeff (2 * i + 1) (2 * j)
          simpa [greenWronskianMomentKernel, completedGreenParityJet] using h.symm
      | inr j =>
          have h := polarizedGreenCoefficient_unique hcoeff (2 * i + 1) (2 * j + 1)
          simpa [greenWronskianMomentKernel, completedGreenParityJet] using h.symm

/-- Concrete end-to-end finite positivity with the final analytic input stated
as the division-free two-variable coefficient equation rather than as an
already assembled Hankel Gram representation. -/
theorem hankelPair_posSemidef_of_completedNativeGreenCoefficientEquation
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (moments : ℕ → ℝ)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState)
    (hcoeff : HasCompletedGreenJetCoefficientEquation moments
      (normalizedCompletedGreenState
        completedNativeOperatorCharacteristic
        (completedNativeC3ProductLedgerState xiState)))
    (N : ℕ) :
    (hankelGram moments N).PosSemidef ∧
      (shiftedHankel moments N).PosSemidef :=
  hankelPair_posSemidef_of_completedNativeGreenFactors
    xiState moments hxi hnative
      (complexGreenWronskianMomentKernel_of_coefficientEquation hcoeff) N

end

end CarrySelfAdjointOperator
