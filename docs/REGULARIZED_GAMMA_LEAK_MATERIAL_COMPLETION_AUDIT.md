# Regularized resolved-port/leak versus material/completion

## Checkpoint and status

Initial main: `2dff4668300e7918b1afda4bf8276ddb46ab6eee`.
`git pull --ff-only` reported up to date. HEAD/main/origin/main agreed and
initial working tree was clean. The work stays on main.

Status: `PASS_REGULARIZED_GAMMA_LEAK_MATERIAL_COMPLETION_DEFECT_IDENTITY`.
The pre-existing literal normalized ambient Gram no-go is preserved and
checked against the new expansion. No positive completed kernel is claimed.

## Same vectors, same normalization

The new module `CompletedNativeRegularizedGammaLeakSewing` uses
`CarryGammaComplexNaimark`, the existing complex Hilbert view of both real
Naimark quadratures. No new carrier, inner product, camera weight, or
source amplitude is introduced.

Write `F = completedNativeOperatorCharacteristic`, `A = nativeXiCompletionFactor`,
`Z = nativeHeightScalar`, and let `p,l` be the existing coisometric port and
retained induced-source leak. For nonreal z in the existing half-plane:

```text
u(z) = Gamma(z)p(z) + R(z)l(z)
alpha(z) = (sqrt(2) * F(z))^(-1)
ghat(z) = alpha(z) * Gamma(z)p(z)
dhat(z) = alpha(z) * R(z)l(z)
uhat(z) = ghat(z) + dhat(z).
```

The normalization is exactly the old normalized ambient-response state.
The new two response definitions depend only on the already constructed
completed source, Naimark port/leak split and logarithmic resolvent.
The vectors are synthesized before taking any inner product.

Their four-term readout is defined independently of dslope or moments:

```text
P4(z,w) = inner ghat(z) ghat(w) + inner ghat(z) dhat(w)
          + inner dhat(z) ghat(w) + inner dhat(z) dhat(w).
```

The first argument is conjugate-linear. Both ordered cross terms remain.
No orthogonality after resolvent transport, termwise positivity, bounded
individual central limits, or cancellation of individual channels is assumed.
The new theorem proves `P4 = inner uhat(z) uhat(w)`, exactly the old
normalized ambient response kernel.

## Exact sewing difference and the mandatory characteristic weight

Let

```text
chi(z,w) = 2 * conj(F(z)) * F(w)
s(z,w) = w - conj(z)
M(z,w) = conj(A(z)) * A(w) * canonicalNativeUndressedGreenForm z w
C(z,w) = canonicalArchimedeanBoundaryGreenCorrection z w.
```

`M+C` is the existing product-rule scalar Green readout of the complete
native value/companion pair. Its two components are retained. The earlier
vector theorem `sourceCompanion_eq_native_add_completion` uses the same
product rule in the existing Cauchy source carrier. No inverse of a scalar
trace projection or identification of those two carriers is constructed.

The main new identity is

```text
D4(z,w) / (chi(z,w) * s(z,w))
  = P4(z,w) - (M(z,w) + C(z,w)) / (chi(z,w) * s(z,w)),
```

where D4 is literally the already defined
`canonicalCompletedC3CoisometricWronskianFourChannelDefect`.
This holds for the existing strip and nonreal parameters with nonzero
separation; its algebra does not require a characteristic nonzero premise.
For a meaningful normalized dslope comparison, the next theorem additionally
requires `F(z) != 0`, `F(w) != 0` and proves

```text
(M+C)/(chi*s) = canonicalCompletedNativePolarizedDslopeKernel z w
D4/(chi*s) = P4 - canonicalCompletedNativePolarizedDslopeKernel z w.
```

Thus the statement is a **difference**, not an equality of the two kernels.
Dividing D4 only by separation would leave the characteristic weight and
would not give the normalized kernel mismatch.

## Existing radial ledger, not a replacement

The old ambient radial grid is used literally:

```text
z(k,N,i) = (i+1) * I / (2*(N+1)*(k+1)).
```

It is not identified with the distinct chiral/Cauchy grid
`(i+1)*I/(k+1)`. The pointwise theorems are available on either regular
family, but this radial specialization uses the first grid only.

The kernel proves, for each existing finite entry:

```text
canonicalCompletedC3RegularizedAmbientRadialDslopeDefect = P4 - dslope.
```

After the already proved eventual nonvanishing of F, it also proves

```text
canonicalCompletedC3RegularizedAmbientRadialCorrectionLedger
  eventually equals P4 - (M+C)/(chi*s).
```

This is the old full ledger with its existing four geometric channels;
no fitted residual or new ledger replaces it. The proof works for every
cutoff M and every finite entry. It makes no assertion that each of the
four old correction channels corresponds one-to-one to a port/leak pairing.
Four correction channels and four Gram terms are different decompositions.
Nor does it identify completion with leak.

## Central diagnostic and limit of the result

The source-first comparison is closed before any canonical moment comparison.
In the dedicated audit, a separate diagnostic uses the pre-existing theorem
`canonicalCompletedC3RegularizedAmbientRadialDslopeDefect_tendsto_centralExcess`
to check that the new `P4-dslope` expression has that same central limit.
The existing `canonicalCompletedC3NormalizedAmbientCentralExcess_pos` is
reused; its positivity is not reproved or used in the new source-first roots.

Hence the literal normalized ambient Gram retains its strictly positive
central mismatch. This calculation cannot make it vanish by rearranging
resolved-leak/material/completion terms. It does not refute a distinct
geometric compression or signed realization.

The analysis now accounts exactly for the full difference, but does not
locate the positive central excess in any one individual pairing. Separate
central limits of the resolved port and resolved leak are not claimed.
The earlier global port-only obstruction and literal ambient radial Gram
no-go remain distinct results with distinct quantifiers.

One remaining geometric question: is there an existing source-derived
compression/return map whose complete polarized readout removes this
mismatch? No such map, metric, complement or sign hypothesis is postulated
here. Matching the scalar readouts is not a vector intertwiner.

## Public declarations

Three definitions and eight theorems:

- `canonicalCompletedC3NormalizedGammaPortResponse`;
- `canonicalCompletedC3NormalizedResolvedLeakResponse`;
- `canonicalCompletedC3NormalizedAmbientResponse_eq_gammaPort_add_resolvedLeak`;
- `canonicalCompletedC3NormalizedGammaLeakPairing`;
- `canonicalCompletedC3NormalizedAmbientKernel_eq_gammaLeakPairing`;
- `canonicalCompletedC3RegularizedFourChannel_eq_gammaLeak_sub_materialCompletion`;
- `canonicalCompletedC3RegularizedFourChannel_eq_gammaLeak_sub_dslope`;
- `canonicalCompletedC3RegularizedAmbientDefect_eq_gammaLeak_sub_dslope`;
- `canonicalCompletedC3Dslope_eq_materialCompletion_div`;
- `canonicalCompletedC3RegularizedAmbientDefect_eq_gammaLeak_sub_materialCompletion`;
- `canonicalCompletedC3RegularizedLedger_eventually_eq_gammaLeak_sub_materialCompletion`.

## Trust and validation

The dedicated source dependency firewall passed all 11 roots: 6482 reachable
declarations, only `[propext, Classical.choice, Quot.sound]`. No canonical
moment target, HP/Stieltjes certificate, Hankel/Jacobi-height positivity,
Herglotz input or BR2 declaration is reachable from these roots. Imported
historical modules are not confused with reachable proof dependencies.
The separately labeled diagnostic reuses the old moment/excess comparison;
it is outside the source firewall and is not an input to any root above.

Finite canaries `(0,0)`, `(0,1)`, `(1,1)` on Fin 2 pass exactly with the
existing ambient grid and characteristic normalization. They retain the
kernel mismatch instead of setting it to zero.

Validation commands:

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedNativeRegularizedGammaLeakSewing
lake build --wfail CarrySelfAdjointOperator.CompletedNativeRegularizedGammaLeakSewingAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

Focused logs on llm: `/tmp/regularized-gamma-leak-build.log`,
`/tmp/regularized-gamma-leak-audit.log`. Full validation logs are retained in
`/tmp/regularized-gamma-leak-validation/`. All listed validation commands passed before publication; the complete
result is `FULL_VALIDATION_PASSED` and the full script ended with
`kernel audit passed`. Placeholder/control scans and `git diff --check`
also passed. Final Git agreement is recorded in the delivery.

Changed files: new theorem/audit modules, root imports, theorem registry,
this report, README and the append-only checkpoint. No dependency source,
Foundation, metric, old canonical object or upstream checkout is modified.
