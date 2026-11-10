# Cross-repository audit — source-first C2 all-order

Audited 2026-11-10 from the actual Lean sources before reading the research
notes. The hashes below identify the source snapshots examined; local clones
of Primos and Geometry-of-Numbers were older and dirty, so the fetched remote
`main` trees were inspected with `git show` without changing those worktrees.

## Repository snapshots

| Repository / reference | SHA examined | Evidence |
|---|---|---|
| `primos` `main` / PR #47 merged | `e2a723b4ec3e645539de0b9ca881951d93259cda` | Remote `ls-remote`; GitHub PR page says merged; Lean files read from this tree |
| `geometry-of-numbers` `main` / PR #41 merged | `8f5631a7808ad7c73491b558a894566e1d39899c` | Remote `ls-remote`; GitHub PR page says merged; six Lean source files read |
| `momentos` `research/sigma-pade-dimension-depth-20261104` | `eeac8c13581e026df409886751a9368ff05d488d` | Remote branch fetched; requested research notes and exact test script read |
| CSA research worktree | `eb4077b55fa8086af154e2ae94a0a7cdaae80387` | Clean at audit start on `agent/allorder-pencil-cofactor-euler-20261110` |
| CSA remote research branch before this continuation | `6135f447039db503b0252d0a814b2b698b19ce54` | `ls-remote`; prior local commits are ahead, not force-pushed |

The coefficient ceiling and 4×4 bridges are recorded at CSA commit
`0974fe6dde468da822a35b6489b3d8135cd6618d`; the order-three source gate is
recorded at `939aa3aacb8154a740c81d3e3648fe3b3473db9f` on the same branch.

The public GitHub page for Momentos PR #2 returned 404 in the browser, but the
requested research branch was reachable through the configured Git remote.
The contents below are therefore attributed to the fetched branch SHA, not to
an unaudited PR webpage.

## Primos PR #47 — source declarations read

Files were read from the SHA above, not the stale local clone:

- `CpPrimeTowerCarryMangoldtBridge.lean`: `primeVerticalScale_prime_pow`,
  `primeVerticalScale_eq_depth_mul_vonMangoldt`,
  `allPrimeCameraAtomicLedger_eq_divisorMangoldtLedger`.
- `CpPrimeDepthLogWaveBridge.lean`: `primeDepthLogCoordinate_eq_log`,
  `nativeCarryLogWave_primeDepthLogCoordinate_eq_dirichletTerm`,
  `finiteChart_primeDepthWave_eq_dirichlet`, and
  `primeDepthWaveCharacteristic_iff_resonance`.
- `CpPrimeDepthFiniteDerivativeBridge.lean`:
  `hasDerivAt_natDirichletTerm_eq_neg_log`,
  `hasDerivAt_finiteChart_dirichlet_eq_neg_mangoldt`, and
  `neg_deriv_finiteChart_dirichlet_eq_atomicPrimeCamera`.
- `CpGenuineTiltProductRule.lean`: `centeredSecondDifference_mul` and
  `centeredSecondDifference_localDirichletProfile_eq_weightedTilt_add_carrier`.
  The latter retains a carrier-curvature term and two first-difference cross
  terms alongside the weighted tilt.
- `CpC2DirichletJetTfvd.lean`:
  `c2OddCoreDirichletLogSpectralGap_eq_connectedCumulant_mul`,
  `c2OddCoreDirichletLogTfvdReadout_eq_spectralGap`, and the exact
  `c2OddCoreDirichletLogTfvdReadout_eq_logCoefficient_mul` crosswalk.
- `CpTfvdGenuineCarryIdentification.lean`:
  `enrichedTfvdGenuineBracketReadout_canonical_eq_weightedTilt_add_carrierRemainder`.

Classification: these are exact carry/Mangoldt, derivative, connected
cumulant, and finite TFVD scalar identities. They do not construct a positive
inner product for the completed logarithmic derivative moments, and they do
not identify the two C2 product-rule cross terms with a Hankel Gram energy.
The stencil identity is local to the material/Dirichlet field; transporting
that energy through completion remains a separate obligation.

## Geometry-of-Numbers PR #41 — source declarations read

- `MomentFunctional.lean`: `momentForm_symm`,
  `momentForm_multiply_X`, `residualPolynomial_pairing`,
  `orthogonalPolynomial_self`, and `orthogonalPolynomial_residual_orthogonal`.
  Symmetry and signed residual pairing do not assume positivity; the latter
  orthogonality theorem requires preceding pivots to be nonzero.
- `PolynomialCoordinates.lean`:
  `residualPolynomial_monic_degree`,
  `polynomial_coordinates_independent`, and `momentPolynomialBasis_apply`.
  The monic polynomial basis exists for arbitrary real moment data, including
  degenerate and indefinite forms.
- `SchurLogic.lean`: `sourceMomentSchur_sewing_of_isUnit`,
  `sourceMomentSchur_critical_direction_of_isUnit`, and
  `native_inverseSchur_boundary_energy`. The original sewing/energy identity
  needs invertibility, not `PosDef`.
- `JacobiLogic.lean`: `transport_isSymm_of_isSymm` and
  `finiteJacobiSection_isSymm_unconditional` are symmetry-only;
  `exists_whitening_iff_posDef` shows exact real whitening is equivalent to
  positive definiteness.
- `NativeApplication.lean`: `native_boundary_polynomial_energy` and
  `native_residual_self` apply signed polynomial energies to the canonical
  completed source; no positivity is asserted by those equalities.
- `Controls.lean`: `controlLogMoments_negative_pivot` gives pivot `-18`;
  `future_zero_not_radical` separates isotropy from the global radical;
  `rotation_no_real_eigenvector` and `negativePoint_no_positive_height`
  prevent interpreting an indefinite pencil as a positive-metric height
  operator.

Classification: PR #41 removes unnecessary `PosDef` hypotheses from algebraic
orthogonalization and Schur sewing when the correct hypothesis is `IsUnit`.
It does not supply source signs and explicitly keeps whitening/positive-height
claims conditional on positive definiteness.

## Momentos PR #2 branch — notes and exact controls read

The seven requested notes were read after the source files above. They record
paper algebra and research controls, not new Lean compilation. In particular:

- `INDUCAO_ARBITRARIA_PENCIL_COFACTOR_EULER_THETA_20261110.md` states the
  pencil/cofactor, vector energy, Toda, and theta-energy identities and points
  to `scripts/verify_all_n_pencil_cofactor_toda.py` for finite exact checks.
- The source gate remains the two integrated mass comparisons; signed Green
  densities have negative regions, and the odd Schur channel has nonzero
  negative mass at every order.
- `CENTRO_HANKEL_FONTE_EULER_PROJECAO_NO_GO_20261110.md` preserves the
  finite-head counterexample and says explicitly that the research proof does
  not establish universal Hankel positivity.
- `GAP_ESTRUTURAL_DIRECAO_QUE_ANULA_DEZ_MODOS_20261110.md` identifies the
  projected residual energy as the first obstruction after annihilating a
  finite positive head; this is a condition to prove, not a source fact.
- `ATAQUE_ALL_ORDER_GREEN_WRONSKIAN_PICK_20261110.md` leaves the canonical
  completed gamma-Cauchy scalarization as a hypothesis and does not produce a
  Gram realization of the completed kernel.

The exact rational test and its no-go control are run separately and their
results are recorded in `CHECKPOINT.md`. Finite checks do not prove the
dimension-arbitrary identities.

## CSA declarations inspected

The all-order source definitions in `NativeSourceAllOrderSchur.lean`, the
cofactor and bordered integral in `NativeThetaCofactorMargin.lean`, the Euler
balances, convolution cancellation, theta masses, Green transport, and the
conditional two-tower induction were read directly. The canonical source
identification `primeDepthGeometricMoment_eq_canonical` is proved by uniqueness
of the log-derivative recurrence after defining an independent response
sequence; it does not use zeros or a preselected positive measure.

Current state distinction:

- `PROVADO_LEAN`: pencil/cofactor polynomial identity, critical vector
  multiplication and energy, cofactor theta integral as a determinant
  product, conditional all-order Euler gates, finite order-two Euler gates,
  and the order-two-to-three mass-deficit audit.
- `PROVADO_LEAN`: the all-order characteristic-ceiling equivalence is now
  compiled and audited for every `s,n`; the source discriminants are linked
  to both 4×4 Hankel determinants with exact factor 16. The central 4×4
  determinant is positive by the existing source certificate. The resulting
  even Euler mass gate at `n=3` is also proved without assuming 4×4 `PosDef`.
- `PARTIAL`: Toda is compiled only at `n=1`; the general division-free
  Desnanot–Jacobi step is open. The shifted 4×4 determinant is equivalent to
  the explicit strict `c₈` ceiling, whose truth is not established. The odd
  Euler mass gate at `n=3` is equivalent to the general ceiling
  `c₈ < nativeSourceCharacteristicCeiling 1 3`.
- `ABERTO`: general source mass dominance; no completed Green-Wronskian Gram
  representation; the next shifted tower sign remains open.

Since the initial audit, the new Lean module
`NativeAllOrderFiniteDiscriminantBridge.lean` has now proved both 4×4
determinant identities with factor 16. The central determinant is positive by
the existing order-14 source certificate. The shifted determinant is
equivalent to the existing strict ceiling bound for `c₈`; that bound is not
proved. The new `NativeAllOrderCharacteristicCeiling.lean` gives the explicit
all-order ceiling for every shift and dimension.

Tests rerun from this branch SHA:

- `verify_all_n_pencil_cofactor_toda.py` rational checks: 63 exact cases passed
  for dimensions 0–6 and shifts 0–2, including negative values and singular
  prefixes. The symbolic sweep in that script was not part of this recorded
  run; the Lean general theorem remains the evidence for arbitrary dimension.
- `verify_signed_tail_no_go.py`: 18 exact `Fraction` checks passed for ranks
  1–6 and shifts 0, 1, 3.
- `exact_fourier_positive_hankel_countermodel.py`: exact expected moments and
  minors passed; the 4th consecutive 2×2 minor is
  `-1274953/268240896000` despite a positive Fourier measure. This is an
  auxiliary counterexample to a proof strategy, not to the C2 source.
- Local `test_allorder_exact_regressions.py`: 126 exact `Fraction` cases passed
  across six positive/signed/singular/indefinite sequences, `n=0..6`, and
  shifts `s=0..2`; it checks polynomial pencil/cofactor values, vector energy,
  orthogonality, and Toda. This remains finite regression evidence only.

The three new Lean modules and their `#print axioms` audit files were recompiled
with focused `lake env lean` commands from the existing CSA build cache, using
the research worktree as `--root`; all six returned exit code 0. Running from
the isolated worktree itself first failed only because that worktree lacks the
legacy `.olean` cache. The complete Lake build remains unverified.

The subsequent order-three source gate is recorded at CSA commit
`939aa3aacb8154a740c81d3e3648fe3b3473db9f`. It proves the central even mass
gate and reduces the next odd mass gate exactly to the `c₈` ceiling. A
non-rigorous direct-characteristic Cauchy/DFT diagnostic at 80 decimal digits,
with two radii/sample counts, gives margin about `1.8407523191e-24`; it is not
an interval certificate or Lean theorem. The existing absolute coefficient
bound for `c₈` is about `4.68e-12`, far too coarse to certify that margin.

No source definition, dependency pin, or moment definition was changed by this
audit.
