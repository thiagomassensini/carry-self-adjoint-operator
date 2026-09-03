import CarrySelfAdjointOperator.DivisionFreeGreenConfinement
import CarrySelfAdjointOperator.CompletedNativeChiralCayleyHerglotz
import Mathlib.Tactic

/-!
# Height-channel realization of the finite native-carry Green form

The finite native-carry *camera* Green form (in `NativeCarryC3Crosswalk`,
`greenForm(port r, port s) = (λ(s) − conj λ(r)) · ⟨∇r, ∇s⟩`) already has the
exact algebraic shape of a division-free Green representation, but written in
the *eigenvalue* variable `λ = natDirichletTerm · 3`.  The completed **height**
gate `HasDivisionFreeGreenRepresentation` is the same identity with the
spectral variable equal to the height parameter itself (factor `z − conj w`).

This file carries the finite form's purely algebraic Gram reduction
(`scalarBoundaryResponse_kernel_eq_gram_of_greenWronskian`) into the height
channel.  Using the completed characteristic `F` and its fixed boundary
companion `Psi = −F'`, it proves: on every regular separated pair, the
Herglotz/Pick kernel of `a = −F'/F` equals a **manifest Hilbert Gram** of the
normalized states `F(·)⁻¹ • state(·)` — *provided* the single operator-domain
Green identity

`completedGreenWronskian F (−F') z w = (z − conj w) · ⟨state w, state z⟩`

holds.  That identity is exactly `HasDivisionFreeGreenRepresentation`, the
all-order gate; it is **not** proved here.  What is unconditional is the
transport: once the finite geometry (or any source) supplies the Green
identity, the height Herglotz kernel is positive by construction.
-/

open scoped ComplexConjugate

namespace CarrySelfAdjointOperator

noncomputable section

/-- Divided boundary response of the completed characteristic.  For the fixed
companion `Psi = -F'` this is definitionally the Herglotz coordinate
`a = -F'/F`. -/
def completedNativeGreenBoundaryResponse (z : ℂ) : ℂ :=
  completedNativeOperatorBoundaryCompanion z /
    completedNativeOperatorCharacteristic z

@[simp] theorem completedNativeGreenBoundaryResponse_eq_logDerivativeCoordinate
    (z : ℂ) :
    completedNativeGreenBoundaryResponse z =
      completedNativeLogDerivativeHerglotzCoordinate z :=
  rfl

/-- Algebraic passage from the division-free completed Green Wronskian to the
divided Herglotz difference, wherever the characteristic is nonzero and the
two parameters are separated.  This is the height-channel form of the finite
camera identity `scalarBoundaryResponse_sub_star_div`. -/
theorem completedNativeGreenBoundaryResponse_sub_star_div
    (z w : ℂ)
    (hz : completedNativeOperatorCharacteristic z ≠ 0)
    (hw : completedNativeOperatorCharacteristic w ≠ 0)
    (hzw : z ≠ (starRingEnd ℂ) w) :
    (completedNativeGreenBoundaryResponse z -
          (starRingEnd ℂ) (completedNativeGreenBoundaryResponse w)) /
        (z - (starRingEnd ℂ) w) =
      completedGreenWronskian completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z w /
        ((z - (starRingEnd ℂ) w) *
          completedNativeOperatorCharacteristic z *
            (starRingEnd ℂ) (completedNativeOperatorCharacteristic w)) := by
  unfold completedNativeGreenBoundaryResponse completedGreenWronskian
  have hwstar :
      (starRingEnd ℂ) (completedNativeOperatorCharacteristic w) ≠ 0 := by
    intro hzero
    apply hw
    have h := congrArg (starRingEnd ℂ) hzero
    simpa using h
  rw [map_div₀]
  field_simp [hz, hwstar, sub_ne_zero.mpr hzw]

/-- **Height-channel realization of the finite Green form.**  Given the single
operator-domain Green identity, the Herglotz/Pick kernel of `a = -F'/F` is a
manifest Hilbert Gram of the normalized states `F(·)⁻¹ • f(·)`.  This is the
gate expressed as one positive realization; it is not proved here. -/
theorem completedNativeHerglotzKernel_eq_gram_of_greenWronskian
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (f : ℂ → H) (z w : ℂ)
    (hz : completedNativeOperatorCharacteristic z ≠ 0)
    (hw : completedNativeOperatorCharacteristic w ≠ 0)
    (hzw : z ≠ (starRingEnd ℂ) w)
    (hgreen :
      completedGreenWronskian completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z w =
        (z - (starRingEnd ℂ) w) * inner ℂ (f w) (f z)) :
    (completedNativeLogDerivativeHerglotzCoordinate z -
          (starRingEnd ℂ)
            (completedNativeLogDerivativeHerglotzCoordinate w)) /
        (z - (starRingEnd ℂ) w) =
      inner ℂ ((completedNativeOperatorCharacteristic w)⁻¹ • f w)
        ((completedNativeOperatorCharacteristic z)⁻¹ • f z) := by
  rw [← completedNativeGreenBoundaryResponse_eq_logDerivativeCoordinate,
    ← completedNativeGreenBoundaryResponse_eq_logDerivativeCoordinate,
    completedNativeGreenBoundaryResponse_sub_star_div z w hz hw hzw, hgreen]
  have hwstar :
      (starRingEnd ℂ) (completedNativeOperatorCharacteristic w) ≠ 0 := by
    intro hzero
    apply hw
    have h := congrArg (starRingEnd ℂ) hzero
    simpa using h
  simp only [inner_smul_left, inner_smul_right, map_inv₀]
  field_simp [hz, hwstar, sub_ne_zero.mpr hzw]

/-- **Consolidated bridge.**  A full division-free Green representation of the
completed characteristic makes the Herglotz kernel of `-F'/F` a manifest Gram
at every regular separated pair.  This is the height analog of the finite
camera Green form: the arithmetic geometry supplies the Green identity shape,
and this theorem transports it to positive kernel structure.  Supplying the
representation itself is the all-order (RH-equivalent) gate. -/
theorem completedNativeHerglotzKernel_eq_gram_of_divisionFreeGreen
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {state : ℂ → H}
    (hgreen : HasDivisionFreeGreenRepresentation
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion state)
    (z w : ℂ)
    (hz : completedNativeOperatorCharacteristic z ≠ 0)
    (hw : completedNativeOperatorCharacteristic w ≠ 0)
    (hzw : z ≠ (starRingEnd ℂ) w) :
    (completedNativeLogDerivativeHerglotzCoordinate z -
          (starRingEnd ℂ)
            (completedNativeLogDerivativeHerglotzCoordinate w)) /
        (z - (starRingEnd ℂ) w) =
      inner ℂ ((completedNativeOperatorCharacteristic w)⁻¹ • state w)
        ((completedNativeOperatorCharacteristic z)⁻¹ • state z) :=
  completedNativeHerglotzKernel_eq_gram_of_greenWronskian
    state z w hz hw hzw (hgreen z w)

/-- Elementary identity: the divided difference of a value against its own
conjugate collapses to the ratio of imaginary parts. -/
private theorem sub_conj_div_sub_conj_eq (ζ w : ℂ) (hw : w.im ≠ 0) :
    (ζ - (starRingEnd ℂ) ζ) / (w - (starRingEnd ℂ) w) =
      ((ζ.im / w.im : ℝ) : ℂ) := by
  rw [Complex.sub_conj, Complex.sub_conj]
  push_cast
  have hwim : (w.im : ℂ) ≠ 0 := by exact_mod_cast hw
  field_simp

/-- **Diagonal Herglotz positivity.**  Off the real axis, a division-free Green
representation forces the Herglotz coordinate `a = -F'/F` to be genuinely
Herglotz: `Im a(z) / Im z` equals the diagonal Gram value of the normalized
state.  This is exactly the positivity the height gate asserts, exhibited as a
Gram diagonal — the finite Green form's arithmetic, carried to the height
channel. -/
theorem completedNativeLogDerivative_im_div_eq_inner_re_of_divisionFreeGreen
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {state : ℂ → H}
    (hgreen : HasDivisionFreeGreenRepresentation
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion state)
    (z : ℂ)
    (hz : completedNativeOperatorCharacteristic z ≠ 0)
    (hzim : z.im ≠ 0) :
    (completedNativeLogDerivativeHerglotzCoordinate z).im / z.im =
      (inner ℂ ((completedNativeOperatorCharacteristic z)⁻¹ • state z)
        ((completedNativeOperatorCharacteristic z)⁻¹ • state z)).re := by
  have hzconj : z ≠ (starRingEnd ℂ) z := by
    intro h
    apply hzim
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  have hkernel :=
    completedNativeHerglotzKernel_eq_gram_of_divisionFreeGreen
      hgreen z z hz hz hzconj
  rw [sub_conj_div_sub_conj_eq _ z hzim] at hkernel
  have h2 := congrArg Complex.re hkernel
  rwa [Complex.ofReal_re] at h2

/-- Consequently the Herglotz coordinate satisfies the sign gate off axis:
`0 ≤ Im a(z) / Im z`. -/
theorem completedNativeLogDerivative_im_div_nonneg_of_divisionFreeGreen
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {state : ℂ → H}
    (hgreen : HasDivisionFreeGreenRepresentation
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion state)
    (z : ℂ)
    (hz : completedNativeOperatorCharacteristic z ≠ 0)
    (hzim : z.im ≠ 0) :
    0 ≤ (completedNativeLogDerivativeHerglotzCoordinate z).im / z.im := by
  rw [completedNativeLogDerivative_im_div_eq_inner_re_of_divisionFreeGreen
    hgreen z hz hzim]
  have h := @inner_self_nonneg ℂ H _ _ _
    ((completedNativeOperatorCharacteristic z)⁻¹ • state z)
  simpa using h

end

end CarrySelfAdjointOperator
