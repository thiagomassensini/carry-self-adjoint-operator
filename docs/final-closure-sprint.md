# Final closure sprint

Living notes for the autonomous attempt to close the positivity gate that
stands between the completed native characteristic and the downstream
critical-line confinement theorem.

Start commit: `9fa1187` (`identify Riesz normal of symplectic crossing`).
Working branch: `agent/final-closure-sprint`.

Rules honored: no `sorry`, `admit`, new axioms, hidden numerical hypotheses,
fitted weights, or chosen constants. Numbers used only to recognize identities,
never as proof.

## 1. The capstone and the exact gate

Downstream capstone: `ConditionalCriticalLineConfinement.lean`,
`riemannZeta_zero_re_eq_half_of_canonicalGreenState` (and siblings). Each needs
one of the equivalent hypotheses in `DivisionFreeGreenConfinement.lean`, the
strongest reduction being

`HasCanonicalCompletedNativeOperatorOffAxisDiagonalGreenEnergy energy`
`  := ∀ z, z.im ≠ 0 →`
`     completedGreenWronskian F (-F') z z = (z - conj z) * (energy z)`

together with `energy(zero) ≠ 0`.

Diagonal computation. With `F = completedNativeOperatorCharacteristic` and
`Psi = -F'`,

`completedGreenWronskian F (-F') z z = A - conj A`,  `A = -F'(z) conj(F z)`,

so it is purely imaginary, `= 2i·Im(F(z) conj F'(z))`; and `z - conj z = 2i·Im z`.
Hence the identity forces

`energy(z) = Im(F(z) conj F'(z)) / Im z = |F(z)|² · Im(a(z)) / Im z`,
`a(z) := -F'(z)/F(z)`.

Therefore the gate is exactly **`a = -F'/F` is a Herglotz/Nevanlinna function**
(`Im a / Im z ≥ 0`), equivalently the diagonal Green energy is nonnegative,
equivalently the chiral Pick kernel is positive semidefinite, equivalently the
log-derivative moment Hankel matrices are PSD at all orders. For the completed
zeta this is RH-equivalent.

At a zero `F(z)=0` the diagonal Wronskian vanishes, so any energy realizing the
identity is `0` there — hence the naive real-part energy cannot satisfy
`energy(zero) ≠ 0`. A state that is nonzero at the zero and satisfies the
diagonal identity would force `z` real, which is the confinement conclusion
itself. Building such a state is equivalent to proving the Herglotz gate.

## 2. Route tree

| Route | Idea | Strongest existing object | Obstruction |
|---|---|---|---|
| 1 | Full polarization → chiral grams | `CompletedC3FullWronskianPolarization` | signed difference `E₊-E₋`; sign not fixed by isometry |
| 2 | Contractive multiplier `I - C*C ≥ 0` | `CompletedNativeRadialChiralMultiplier` | contractivity = the Pick gate (assumed, not proved) |
| 3 | Expanded structural PSD block / Schur | `CompletedNativeExpandedStructuralBlockProbe` | block PSD, but readout is `(+1,-1)` signature, not a compression |
| 4 | dslope PSD directly | `CompletedC3FullWronskianChiralDslope` | dslope = separation × signed chiral difference; PSD not supplied |
| 5 | Herglotz of `-F'/F` | `CompletedNativeChiralCayleyHerglotz` | this *is* the gate |
| 6 | Radial/local germ eventual PSD | `CompletedNativeHerglotzFourthOrderGate` | reduces to positivity of moments `h_n` |
| 7 | Moment/Hankel direct | `CompletedGreenMomentJets` | needs Gram realization of moment kernel = Green state = gate |
| 8 | Jacobi/Weyl inverse | `CanonicalFiniteHeight`, `FiniteJacobiTransport` | Jacobi built *from* the same Hankel PSD (circular) |
| 9 | Coisometry/frame/Naimark | `CompletedC3CoisometricChiralEnergyBlock` | old escape leak is zero; full carrier does not add a legitimate projection |
| 10 | Provenance quotient | (primos `CpMinimalProvenanceQuotient`) | quotient preserves data but supplies no positivity |
| 11 | Hessian / second variation | — | second variation is another signed form, same sign gate |
| 12 | Clock quotient | `CompletedNativeProductClockQuotientGreenAudit` | different carrier; no genuine intertwiner |
| 13 | Theta / xi representation | `CompletedNativeXiThetaCosineRepresentation` | factorwise Green too strong; product characteristic needed |
| 14 | Cross-repo structural import | primos / atlas / green-frame | only abstract architecture, no arithmetic-free positivity |

## 3. What was proved in this sprint (ROTA 1)

New module `CompletedC3FullWronskianCentralChiralEnergy.lean`. `J_full` is a
skew-adjoint isometry, `H = -i J_full` a self-adjoint involution, `P± = (I±H)/2`
orthogonal polarizations (all pre-existing). New unconditional theorems:

- `inner_canonicalCompletedC3FullWronskianCentralState_operator_eq_zero`:
  `⟪X₀, J_full X₀⟫ = 0` (cutoff-free `B_total(0)=0`).
- `canonicalCompletedC3FullWronskianCentralState_chiralEnergies_eq`:
  `‖P₊ X₀‖² = ‖P₋ X₀‖²` (signed resultant `E₊-E₋=0`).
- `canonicalCompletedC3FullWronskianCentralState_chiralEnergies_pos`:
  `0 < ‖P₊ X₀‖²` and `0 < ‖P₋ X₀‖²` (from `X₀ ≠ 0`).
- `..._positiveChiralEnergy_eq_half` / `..._negativeChiralEnergy_eq_half`:
  each equals `‖X₀‖²/2`.
- `canonicalCompletedNativeLogDerivativeMoment_zero_eq_polarized_chiral_crossing`:
  `h₀ = i(⟪P₊X₀,P₊T⟫ - ⟪P₋X₀,P₋T⟫) / D(0)` — the polarized first variation,
  replacing the Riesz-normal projection with no chosen scale.
- `canonicalCompletedC3FullWronskianCentralChiralBalanceVariation_eq_zero_iff`:
  the polarized balance variation vanishes **iff** `h₀ = 0`.

Axioms: `[propext, Classical.choice, Quot.sound]` only. `--wfail` clean.

## 4. The formal obstruction (why ROTA 1 does not close the gate)

The polarization splits the crossing readout into `E₊ - E₋`, with the two
chiral channels honest positive Gram energies. At the center they are **equal**
(`E₊ = E₋ > 0`); the completed logarithmic-derivative information sits entirely
in the **first variation** of their signed difference, which equals `h₀` up to
the fixed denominator `D(0)`. The isometric/symplectic polarization fixes the
two energies to be equal at the center but does not determine the sign of the
first variation. That sign is exactly the Herglotz positivity gate.

This is the same obstruction as the Riesz-normal audit's
`..._CrossingNormalEnergy_eq_h0_iff_of_ne`, where equality with `h₀` required
the arbitrary scale identity `‖n‖² = ‖D(0)‖² h₀`: the polarization removes the
arbitrary scale but not the missing sign.

## 5. Conclusion

Smallest irreducible remaining gate: **positivity of the diagonal Green energy
`Im(a(z))/Im z ≥ 0` for `a = -F'/F` = completed native operator logarithmic
derivative** — equivalently Herglotz of `a`, chiral Pick PSD, or all-order
moment Hankel PSD. Every internal route reduces to this same signed-difference
positivity and none supplies it from the existing isometric, symplectic, Gram,
compression, or quotient structure. Status: **EXHAUSTED with a precise gate**,
plus a green formalized reorganization (ROTA 1) that canonicalizes the gate as a
sign of a first variation of a balanced pair of positive chiral energies.
