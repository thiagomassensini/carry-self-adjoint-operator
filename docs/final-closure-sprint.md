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
| 9 | Coisometry/frame/Naimark | `CompletedC3CoisometricChiralEnergyBlock` | sewing needs `E₊-E₋ = ambient gradient energy`; ambient term is the exact defect at zeros |
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
- `canonicalCompletedNativeLogDerivativeMoment_zero_pos`: `0 < h₀`,
  unconditionally (theta/cosine low-order closure).
- `canonicalCompletedC3FullWronskianCentralChiralBalanceVariation_ne_zero`:
  **unconditional transversality** — the polarized central chiral balance
  variation is nonzero, so the center is a genuine simple crossing of the two
  equal positive chiral energies.

Axioms: `[propext, Classical.choice, Quot.sound]` only. `--wfail` clean.

## 3b. What the repository already closed unconditionally (theta route)

Riemann's positive theta density gives, without RH:

- `canonicalCompletedNativeLowOrderHerglotzCurvaturePositive` (`0<h₀`, `0<h₁`);
- `canonicalCompletedNativeRadialHerglotzSampleMatrix_two_eventually_posSemidef`
  and the chiral Pick two-point analogue;
- `canonicalCompletedNativeHankelGram_one_posDef`,
  `canonicalCompletedNativeShiftedHankel_one_posDef` (the `1×1` sections);
- the first canonical Jacobi/height section
  (`canonicalCompletedNativeGeometricJacobiSectionOne_posDef`).

So the **first section `N=1` (two-point) is unconditionally closed**. The
irreducible gate is the extension to **all orders `N ≥ 2`**
(`hankelGram canonicalCompletedNativeLogDerivativeMoment N` PosDef for all `N`),
equivalently full Herglotz of `-F'/F`. As
`CompletedNativeGeometricLowOrderClosure` states: a genuinely independent proof
"would still have to realize the signed pre-scalarized difference as a positive
defect Gram, after the completion/product channels have been dressed."

The repository's own frontier (`UnconditionalLimitConfinementProbe`) records the
equivalent minimal **sewing seam** `MinimalPublicC3ConfinementSeam`
(`FiniteC3CompletedGreenWronskianSeam 1`) and the stronger completed
scalarization seam `CanonicalCompletedC3GammaCauchyScalarizationSeam`; each
implies `FinalGenuineZeroConfinement`, and neither is asserted unconditionally.

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

## 5. Sharpest form of the gate (coisometric sewing)

`CompletedC3CoisometricWronskianEnergyGate` / `CompletedC3CoisometricChiralEnergyBlock`
give the sharpest scalar form. Define, for off-axis `z` in the strip,

`balance(z) := 2·z.im·(radialCoeff(z)² + 1)·‖DirichletGradientState(z)‖²`
`           - Im(completedGreenWronskian F (-F') z z)`.

Proved unconditionally:

- `..._diagonal_eq_wronskian_iff_energyBalance`: the coisometric compressed
  boundary readout equals the true completed Green Wronskian on the diagonal
  **iff** `balance(z) = 0`.
- `Im(completedGreenWronskian F (-F') z z) = ‖P₊‖² - ‖P₋‖²` (chiral difference).
- At a characteristic zero the Wronskian term vanishes, so
  `balance(z) = 2·z.im·(radialCoeff²+1)·‖DirichletGradientState‖² > 0` off-axis
  (`..._pos_of_characteristicZero`), hence the sewing **fails** at any
  hypothetical off-axis zero (`..._ne_wronskian_of_characteristicZero`).

So the single irreducible gate is the **diagonal sewing identity**

`Im(completedGreenWronskian F (-F') z z)`
`   = 2·z.im·(radialCoeff(z)² + 1)·‖DirichletGradientState(z)‖²`   (off-axis z),

whose left side is the signed chiral difference `E₊ - E₋` and whose right side
is a manifestly nonnegative ambient gradient energy. This is exactly the
diagonal Herglotz/Green positivity `Im(a)/Im z ≥ 0`, `a = -F'/F`, realized as an
energy equality. The ambient gradient energy is precisely the defect by which
the compressed readout diverges from the confinement-relevant Green Wronskian
at a zero; no isometric, symplectic, Gram, compression, coisometric, or
quotient construction in the repository supplies this equality, because
supplying it is equivalent to the Herglotz property (RH-equivalent for the
completed zeta).

## 6. Conclusion

Smallest irreducible remaining gate (three equivalent spellings):

- **Herglotz/diagonal**: `Im(-F'/F(z)) / Im z ≥ 0` for off-axis `z`
  (`a = -F'/F` = completed native operator logarithmic derivative);
- **Chiral/energy**: `E₊ - E₋ = 2·z.im·(radialCoeff²+1)·‖DirichletGradientState‖²`,
  i.e. the signed chiral difference equals the ambient gradient energy;
- **Moment/Hankel**: the log-derivative moment Hankel matrices `(h_{i+j})` are
  PSD at all orders `N ≥ 2` (the `N = 1` section is already unconditional).

Every internal route (1–14) reduces to this same signed-difference positivity;
none supplies it. Status: **EXHAUSTED with a precise gate**, plus a green
formalized reorganization (ROTA 1) canonicalizing the gate as the sign of a
first variation of a balanced pair of strictly positive chiral energies
(`E₊ = E₋ = ‖X₀‖²/2 > 0` at the center; sign of the first variation `= sign h₀`).
