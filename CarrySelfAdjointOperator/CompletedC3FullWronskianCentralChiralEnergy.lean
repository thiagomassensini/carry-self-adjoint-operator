import CarrySelfAdjointOperator.CompletedC3SymplecticCrossingNormalAudit
import CarrySelfAdjointOperator.CompletedNativeXiCosineMomentHerglotzGate
import Mathlib.Tactic

/-!
# Central chiral energy of the completed C3 full Wronskian crossing

This file specializes the canonical polarization of the full completed
Wronskian operator to the cutoff-free central state `X₀` and to the real
source tangent `T`, and records exactly what the polarization supplies.

The full complex structure `J_full` is a skew-adjoint isometry, so the quarter
turn `H = -i J_full` is a self-adjoint involution with orthogonal
polarizations `P± = (I ± H)/2`.  The scalar crossing readout is the signed
difference of the two chiral Gram energies

`(-i) * ⟪X, J_full X⟫).re = ‖P₊ X‖² - ‖P₋ X‖²`.

At the collision the full crossing cancels (`⟪X₀, J_full X₀⟫ = 0`), so the two
chiral energies of the central state are **equal**, and since `X₀ ≠ 0` they are
both **strictly positive**:

`0 < ‖P₊ X₀‖² = ‖P₋ X₀‖² = ‖X₀‖² / 2`.

This is the honest interpretation `E₊ = E₋ > 0` while the signed resultant
`E₊ - E₋` vanishes at the center.

Opening the crossing tangent through the same polarization gives the exact
polarized form of the first collision variation `h₀`:

`h₀ = i (⟪P₊ X₀, P₊ T⟫ - ⟪P₋ X₀, P₋ T⟫) / D(0)`.

## Logical status

Everything here is an algebraic/geometric consequence of the already-proved
isometric polarization and the already-proved collision cancellation.  It does
**not** prove positivity of `h₀`, of the chiral Pick kernel, or of the diagonal
Green energy.  The final theorem
`canonicalCompletedC3FullWronskianCentralChiralBalanceVariation_eq_zero_iff`
isolates precisely why: the sign of the first variation is the sign of `h₀`
itself, which the isometric polarization does not determine.  The two chiral
channels are individually positive Gram kernels; only their **signed
difference** carries the completed logarithmic-derivative information, and the
sign of that signed difference is the remaining gate.
-/

open scoped ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-! ## The central crossing cancels: equal chiral energies -/

/-- The full symplectic crossing of the central state with itself vanishes:
this is the cutoff-free spelling of `B_total(0) = 0`. -/
theorem inner_canonicalCompletedC3FullWronskianCentralState_operator_eq_zero :
    inner ℂ canonicalCompletedC3FullWronskianCentralState
        (canonicalCompletedC3FullWronskianOperator
          canonicalCompletedC3FullWronskianCentralState) = 0 := by
  have h := canonicalCompletedC3FullWronskianOperator_center_collision 0
  rwa [canonicalCompletedC3FullWronskianOperatorState_zero_eq_centralState 0]
    at h

/-- Hence the central chirality balance is exactly zero. -/
theorem canonicalCompletedC3FullWronskianCentralState_chiralityBalance_eq_zero :
    ((-Complex.I) * inner ℂ canonicalCompletedC3FullWronskianCentralState
        (canonicalCompletedC3FullWronskianOperator
          canonicalCompletedC3FullWronskianCentralState)).re = 0 := by
  rw [inner_canonicalCompletedC3FullWronskianCentralState_operator_eq_zero]
  simp

/-- The two chiral energies of the central state are equal.  This is the
signed resultant `E₊ - E₋ = 0` written as an energy identity. -/
theorem canonicalCompletedC3FullWronskianCentralState_chiralEnergies_eq :
    ‖canonicalCompletedC3FullWronskianPositivePolarization
        canonicalCompletedC3FullWronskianCentralState‖ ^ 2 =
      ‖canonicalCompletedC3FullWronskianNegativePolarization
        canonicalCompletedC3FullWronskianCentralState‖ ^ 2 :=
  (canonicalCompletedC3FullWronskian_chiralityBalance_eq_zero_iff _).mp
    canonicalCompletedC3FullWronskianCentralState_chiralityBalance_eq_zero

/-- Because the central state is nonzero, both chiral energies are strictly
positive: `E₊ = E₋ > 0`. -/
theorem canonicalCompletedC3FullWronskianCentralState_chiralEnergies_pos :
    0 < ‖canonicalCompletedC3FullWronskianPositivePolarization
          canonicalCompletedC3FullWronskianCentralState‖ ^ 2 ∧
      0 < ‖canonicalCompletedC3FullWronskianNegativePolarization
          canonicalCompletedC3FullWronskianCentralState‖ ^ 2 :=
  canonicalCompletedC3FullWronskian_chiralEnergies_pos_of_balance_zero
    canonicalCompletedC3FullWronskianCentralState_ne_zero
    canonicalCompletedC3FullWronskianCentralState_chiralityBalance_eq_zero

/-- Each central chiral energy is exactly half of the total central Hilbert
energy. -/
theorem canonicalCompletedC3FullWronskianCentralState_positiveChiralEnergy_eq_half :
    ‖canonicalCompletedC3FullWronskianPositivePolarization
        canonicalCompletedC3FullWronskianCentralState‖ ^ 2 =
      ‖canonicalCompletedC3FullWronskianCentralState‖ ^ 2 / 2 := by
  have hsum :=
    canonicalCompletedC3FullWronskianPolarization_norm_sq
      canonicalCompletedC3FullWronskianCentralState
  have heq := canonicalCompletedC3FullWronskianCentralState_chiralEnergies_eq
  linarith

/-- The negative chiral energy is likewise half of the total. -/
theorem canonicalCompletedC3FullWronskianCentralState_negativeChiralEnergy_eq_half :
    ‖canonicalCompletedC3FullWronskianNegativePolarization
        canonicalCompletedC3FullWronskianCentralState‖ ^ 2 =
      ‖canonicalCompletedC3FullWronskianCentralState‖ ^ 2 / 2 := by
  have hsum :=
    canonicalCompletedC3FullWronskianPolarization_norm_sq
      canonicalCompletedC3FullWronskianCentralState
  have heq := canonicalCompletedC3FullWronskianCentralState_chiralEnergies_eq
  linarith

/-! ## Polarized opening of the crossing tangent -/

/-- The tangent crossing readout of the central state against the real source
tangent is `i` times the signed difference of the two chiral cross-energies. -/
theorem inner_canonicalCompletedC3FullWronskianCentralState_operator_tangent_eq_chiralDifference :
    inner ℂ canonicalCompletedC3FullWronskianCentralState
        (canonicalCompletedC3FullWronskianOperator
          canonicalCompletedC3FullWronskianRealSourceTangent) =
      Complex.I *
        (inner ℂ
            (canonicalCompletedC3FullWronskianPositivePolarization
              canonicalCompletedC3FullWronskianCentralState)
            (canonicalCompletedC3FullWronskianPositivePolarization
              canonicalCompletedC3FullWronskianRealSourceTangent) -
          inner ℂ
            (canonicalCompletedC3FullWronskianNegativePolarization
              canonicalCompletedC3FullWronskianCentralState)
            (canonicalCompletedC3FullWronskianNegativePolarization
              canonicalCompletedC3FullWronskianRealSourceTangent)) :=
  inner_canonicalCompletedC3FullWronskianOperator_eq_polarizationDifference
    canonicalCompletedC3FullWronskianCentralState
    canonicalCompletedC3FullWronskianRealSourceTangent

/-- The Riesz crossing pairing `⟪n, T⟫` is the central operator crossing
`⟪X₀, J_full T⟫`. -/
theorem inner_canonicalCompletedC3FullOperatorCrossingNormal_tangent_eq_central_operator :
    inner ℂ canonicalCompletedC3FullOperatorCrossingNormal
        canonicalCompletedC3FullWronskianRealSourceTangent =
      inner ℂ canonicalCompletedC3FullWronskianCentralState
        (canonicalCompletedC3FullWronskianOperator
          canonicalCompletedC3FullWronskianRealSourceTangent) := by
  rw [← canonicalCompletedC3FullOperatorCrossingFunctional_apply_eq_inner_normal]
  rfl

/-- **Polarized form of the first collision variation.**  The already-proved
identity `h₀ = ⟪n, T⟫ / D(0)` becomes the normalized signed difference of the
two chiral cross-energies.  This is the canonical replacement of the Riesz
normal projection: no scale is chosen, and the old ledger denominator `D(0)` is
the only normalization. -/
theorem canonicalCompletedNativeLogDerivativeMoment_zero_eq_polarized_chiral_crossing :
    (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) =
      Complex.I *
          (inner ℂ
              (canonicalCompletedC3FullWronskianPositivePolarization
                canonicalCompletedC3FullWronskianCentralState)
              (canonicalCompletedC3FullWronskianPositivePolarization
                canonicalCompletedC3FullWronskianRealSourceTangent) -
            inner ℂ
              (canonicalCompletedC3FullWronskianNegativePolarization
                canonicalCompletedC3FullWronskianCentralState)
              (canonicalCompletedC3FullWronskianNegativePolarization
                canonicalCompletedC3FullWronskianRealSourceTangent)) /
        canonicalCompletedC3FullOperatorRealCollisionNormalization 0 := by
  rw [canonicalCompletedNativeLogDerivativeMoment_zero_eq_crossingNormal_tangent,
    inner_canonicalCompletedC3FullOperatorCrossingNormal_tangent_eq_central_operator,
    inner_canonicalCompletedC3FullWronskianCentralState_operator_tangent_eq_chiralDifference]

/-! ## The remaining gate, in polarized language -/

/-- The signed first variation of the polarized chiral balance. -/
def canonicalCompletedC3FullWronskianCentralChiralBalanceVariation : ℂ :=
  Complex.I *
    (inner ℂ
        (canonicalCompletedC3FullWronskianPositivePolarization
          canonicalCompletedC3FullWronskianCentralState)
        (canonicalCompletedC3FullWronskianPositivePolarization
          canonicalCompletedC3FullWronskianRealSourceTangent) -
      inner ℂ
        (canonicalCompletedC3FullWronskianNegativePolarization
          canonicalCompletedC3FullWronskianCentralState)
        (canonicalCompletedC3FullWronskianNegativePolarization
          canonicalCompletedC3FullWronskianRealSourceTangent))

/-- The signed chiral balance variation is exactly the old ledger denominator
times `h₀`. -/
theorem canonicalCompletedC3FullWronskianCentralChiralBalanceVariation_eq_normalization_mul_h0 :
    canonicalCompletedC3FullWronskianCentralChiralBalanceVariation =
      canonicalCompletedC3FullOperatorRealCollisionNormalization 0 *
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  unfold canonicalCompletedC3FullWronskianCentralChiralBalanceVariation
  rw [canonicalCompletedNativeLogDerivativeMoment_zero_eq_polarized_chiral_crossing]
  field_simp
    [canonicalCompletedC3FullOperatorRealCollisionNormalization_zero_ne_zero]

/-- **Exact location of the remaining gate.**  The polarized chiral balance
variation vanishes exactly when the central ruler `h₀` vanishes.  The two
chiral channels `P₊`, `P₋` are individually positive Gram energies with equal
central value, so the isometric polarization determines the balance variation
only up to this single scalar; its sign is the sign of `h₀`, i.e. the
completed logarithmic-derivative positivity gate itself. -/
theorem canonicalCompletedC3FullWronskianCentralChiralBalanceVariation_eq_zero_iff :
    canonicalCompletedC3FullWronskianCentralChiralBalanceVariation = 0 ↔
      canonicalCompletedNativeLogDerivativeMoment 0 = 0 := by
  rw [canonicalCompletedC3FullWronskianCentralChiralBalanceVariation_eq_normalization_mul_h0]
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h
        canonicalCompletedC3FullOperatorRealCollisionNormalization_zero_ne_zero
    · exact_mod_cast h
  · intro h
    exact Or.inr (by exact_mod_cast h)

/-! ## Unconditional transversality from the theta low-order closure -/

/-- The central logarithmic ruler `h₀` is strictly positive, unconditionally.
This is the first completed-native moment, whose positivity is the theta/cosine
(Riemann positive density) low-order closure. -/
theorem canonicalCompletedNativeLogDerivativeMoment_zero_pos :
    0 < canonicalCompletedNativeLogDerivativeMoment 0 :=
  (canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_iff_moments.mp
    canonicalCompletedNativeLowOrderHerglotzCurvaturePositive).1

/-- **Unconditional transversality of the central crossing in polarized
language.**  Combining the theta low-order closure with the polarized crossing
identity: the signed chiral balance variation at the center is nonzero.  The
center is therefore a genuine simple crossing of the two equal chiral energies
`E₊ = E₋ = ‖X₀‖²/2 > 0`; the first variation tilts the balance by exactly
`D(0)·h₀` with `h₀ > 0`.  This closes the low-order (first-section) sign, but
not the all-order Hankel positivity that the downstream confinement requires. -/
theorem canonicalCompletedC3FullWronskianCentralChiralBalanceVariation_ne_zero :
    canonicalCompletedC3FullWronskianCentralChiralBalanceVariation ≠ 0 := fun h =>
  canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne'
    (canonicalCompletedC3FullWronskianCentralChiralBalanceVariation_eq_zero_iff.mp h)

end

end CarrySelfAdjointOperator
