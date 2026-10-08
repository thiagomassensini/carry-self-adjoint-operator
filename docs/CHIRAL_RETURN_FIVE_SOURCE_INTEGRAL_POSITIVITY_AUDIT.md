# Five-coordinate chiral Green boundary: raw source integral sign

## Checkpoint and scope

- Repository: `thiagomassensini/carry-self-adjoint-operator`, `main`.
- Initial verified HEAD/main/origin/main: `9085b6142049fb2c36f99c1041f0ce183d24956d`.
- The tree was clean at the start of the interrupted investigation. Resuming
  preserved its own untracked certificate work; no unrelated edits were present.
- New stable result: **PASS_SOURCE_FIRST_FIVE_BOUNDARY_ENERGY_POSITIVITY**.
- Full five-sample radial storage remains **PARTIAL_SOURCE_FIRST_FIVE_SAMPLE_STORAGE_POSITIVITY**.

This closes the raw-integral sign isolated by the previous checkpoint. It
neither substitutes a boundary truncation for finite-step storage nor
extrapolates to arbitrary sample counts.

## Source and ordering

The original source is unchanged. Its division-free logarithmic derivative,
raw Xi cosine integrals, ninth source jet and exact tenth-order Taylor
remainder were already constructed. In particular,
`radialFifthOddSourceTemplate_synthesis` retains the complete vector synthesis
before mixed readout. This round supplies the next source-integral sign to
that existing construction, without redefining the state or its metric.

Write `a,b,c,d,e,f` for `completedNativeXiCosineMoment 0,...,5`. The polynomial
fixed in the preceding round is

```text
P10 = 105 a² b d f - 180 a² b e² - 350 a² c² f
    + 2520 a² c d e - 2646 a² d³ + 525 a b² c f
    - 2205 a b² d e - 9450 a b c² e + 26460 a b c d²
    - 14700 a c³ d + 14175 b³ c e - 35280 b³ d²
    + 22050 b² c² d.
```

The theorem `nativeSourceTenthMixedNumerator_gt_rational` certifies

```text
P10(a,b,c,d,e,f) > 1/10^13 > 0.
```

No canonical moment sign, HP/Stieltjes certificate, Hankel/Jacobi/height
object, BR2 state, fitted coefficient or new Hilbert metric supplies this
inequality.

## Why the old box obstruction is preserved

`nativeSourceRefinedBox_does_not_force_fiveEvenSign` remains valid. The former
independent Xi integral enclosure really does admit a negative algebraic
witness; that was not a counterexample to the actual source. This proof uses
sharper bounds of the **same theta source** and its exact integrations by
parts. No old theorem is altered.

Let `t_j = completedNativeThetaTailMoment j`. The shared source gives

```text
a = 1/2 - t0/4       b = 2 t0 - t2/4
c = 12 t2 - t4/4     d = 30 t4 - t6/4
e = 56 t6 - t8/4     f = 90 t8 - t10/4.
```

This retains the correlations which an independent Xi box loses.

## Certified quadrature and tails

The existing first mode `thetaFirstMode` and its certified endpoint/weighted
mean nodes are reused, on the same 256 cells of `[0,1]`.

For each cell `[a,b]` a rational lower curvature `gamma` is certified from

```text
f''(u) = (1/4 - 6 pi exp(2u) + 4 (pi exp(2u))²) f(u).
```

The corrected tangent and chord are inequalities for the original function.
Their quadratic corrections are integrated exactly against `u^p`. No
integration weight, amplitude or source is changed.

The higher theta modes retain their original decay before summation:

```text
thetaTail(u) <= thetaFirstMode(u) + 10^-5 exp(-23u),  u >= 0.
```

For `p <= 10`, the first-mode tail beyond `1` is at most `5*10^-11`.
Integrating the higher-mode majorant gives the exact additional bound
`p!/(100000*23^(p+1))`. Gamma's elementary exponential integral identity is
used only for this scalar tail integral, never as a positivity certificate.

The resulting rational theta enclosures are:

| p | Lower | Upper |
|---|---:|---:|
| 0 | 11516610847649/10^15 | 11517085694002/10^15 |
| 2 | 247319466372/10^15 | 247323013292/10^15 |
| 4 | 20000408800/10^15 | 20000749106/10^15 |
| 6 | 2877011042/10^15 | 2877117695/10^15 |
| 8 | 589737312/10^15 | 589803117/10^15 |
| 10 | 0 | 155254655/10^15 |

The six bounds are exact Lean statements, not floating-point evidence.

## Exact polynomial enclosure

The six theta intervals are expressed in unit-cube coordinates solely for a
finite polynomial inequality. This coordinate normalization is not a source
transport, state definition, whitening or change of Hilbert metric.

`CompletedNativeThetaTenthPolynomialEnclosure` expands the original `P10`
after the displayed integrations by parts. Lean `ring` checks every one of
the 175 coefficients. On the unit cube, positive terms are bounded below
by zero and negative terms by their coefficients. Their exact sum is larger
than `10^-13` after undoing the common positive denominator.

The research generator uses exact Python `Fraction` and SymPy arithmetic.
It reuses the eighth-order certified node files and reproduces all new
certificate files. The generator is untrusted: generated inequalities,
expansion identities and all rounding directions are checked by the Lean
kernel. SymPy is needed only to regenerate files, not to build them.

## Formal consequences

The new public source capstones are:

- `nativeSourceTenthMixedNumerator_gt_rational`;
- `nativeSourceTenthMixedNumerator_pos`;
- `nativeSourceFiveEvenDiscriminant_pos`;
- `nativeSourceFiveEvenBoundaryEnergy_pos`;
- `nativeSourceFiveBoundaryEnergy_pos`.

The existing exact discriminant formula gives
`nativeSourceFiveEvenDiscriminant = P10/(4572288000*a^5) > 0`.
The existing square completion then proves strict positivity of the even
three-coordinate face, with **all three crosses retained**, and of the full
five-coordinate face including its odd sector. No new form is fitted.

## Remaining gate

Prove uniform transfer of the already constructed full radial storage to
this now-positive boundary face at cutoff `N=5`: inverse Euler boundary
coordinates, all nodes, exact higher remainder, uniform control on the
finite coefficient unit sphere, then homogeneity. The remainder must remain
in vector synthesis until the complete mixed readout.

This report does not claim full `N=5` storage positivity, all-order
contractivity, Pick/Herglotz/dslope positivity or strictness downstream.

## Audit and reproduction

Dedicated audit: `CompletedNativeChiralReturnTenthSourceIntegralAudit`.
It checks all new public module-level declarations with
`#assert_prime_depth_source_axioms`, `#print axioms`, and the transitive
`#assert_oriented_green_source` firewall. All 32 new module-level public declarations are checked. The 3,072 generated
cell/curvature facts are reached through the integral and source capstones.
The transitive source check visits 5,305 declarations. Only `propext`, `Classical.choice`
and `Quot.sound` are permitted; no trust escape or new axiom is added.

The name firewall originally treated classical Jacobi theta functions as
spectral Jacobi operators. A diagnostic traversal found exactly
`jacobiTheta₂`, `jacobiTheta₂_term`, and `jacobiTheta₂_term._proof_1` in the raw
analytic integral dependencies. The firewall now exempts only these three
Mathlib function declarations. All spectral Jacobi, height, Hankel, HP,
Stieltjes, canonical target moment and BR2 dependencies remain forbidden.
This changes an audit-name classification, not a proof premise.

The focused module/audit build has passed with `--wfail`; the source firewall
and the axiom prints passed. Full-root and script outcomes are recorded
below after their checks complete. The repository root and its Audit import the new gate.

Reproduction:

```bash
python3 research/theta-tenth-source-certificate-generate.py --output-dir /tmp/theta-tenth-regenerated
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnTenthSourceIntegral
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnTenthSourceIntegralAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```


### Final validation outcome

All commands above passed on `llm` with Lean `v4.32.0`, including both root
targets, both audit scripts, and `git diff --check`. The regeneration check
used exact arithmetic locally and reproduced all 56 proof-data modules plus
the integral and polynomial certificates byte-for-byte.

The final transitive source firewall covers 5,305 declarations and the new
axiom prints are within `[propext, Classical.choice, Quot.sound]`.
The focused capstone log is retained at
`research/chiral-five-source-integral-2026-10-08/validation.txt`.
Full logs remain on the server in
`/tmp/chiral-five-source-integral-validation/`.

Files changed: the two source quadrature/tail modules, 56 generated
certificate modules, the integral/polynomial certificate modules, source
positivity and dedicated audit modules, the narrow theta-name audit fix,
root/root-audit imports, the exact generator, README and this report.
No existing source, carrier, scalar readout or metric is changed.
Commits are split by audit classification, quadrature certificates, source
boundary sign and documentation. Push occurs only after the full validation.
