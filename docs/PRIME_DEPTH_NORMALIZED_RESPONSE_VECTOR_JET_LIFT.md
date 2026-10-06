# Prime-depth normalized response vector jet lift

## Checkpoint and status

Initial `HEAD = main = origin/main = GitHub`:
`71accfc85da3427e4cda993fff57e32ab170f746`.
Work is performed on canonical `main`; no experimental branch is used.

Status: `PASS_PRIME_DEPTH_NORMALIZED_RESPONSE_VECTOR_JET_LIFT`.
This means a vector lift with a fixed readout, **not a moment Gram**.

## Inventory before the construction

| Existing object | Domain → codomain / linearity | Retained data and limitation |
|---|---|---|
| `CanonicalC3BracketTfvdCompletionState M` | Structured source at a height parameter | TFVD transport, `valueTail`, `logJetTail`, Green port and boundary provenance; not itself a supplied normed vector space |
| `canonicalC3BracketTfvdNormalizedResponse` and its Taylor coefficients | Complex parameter → complex scalar; nonlinear quotient | Completed head/tail readout, chart and completion; coefficient equality alone is not a vector lift |
| Four-trace/six-source and all-order TFVD intertwiners | Finite structured sources and realified/projective carrier maps | Preserve several source roles; the reflected/radial parts are not assumed holomorphic complex jet carriers |
| `canonicalCompletedC3FullWronskianOperatorState M` | Complex parameter → `CanonicalCompletedC3FullWronskianOperatorCarrier` | Existing complex Hilbert trace projection after complete TFVD head/tail synthesis, with archimedean/chart traces |
| `canonicalCompletedC3FullWronskianStructuralState M role` | Complex parameter → the same Hilbert carrier | Four labels: `head`, `tail`, `xiCompletion`, `chartCorrection`; existing synthesis equals the complete raw state |
| `canonicalCompletedC3FullWronskianOperator` | Fixed continuous linear map on that carrier | Existing symplectic/Wronskian operator; not the material clock and not a positive Gram kernel |
| `completedNativeGreenVectorTriangularAct` | Finite vector prefixes → prefixes, linear with fixed even characteristic coefficients | Uses the even variable grading and a conditional convolution interface; it does not directly include the full chart-times-characteristic scalar germ in this construction |
| `CompletedNativeFirstSecondLayerAudit` | Scalar projective-valve curvature/coefficient layer | Closed scalar genealogy; no ready fixed vector readout for the normalized all-order jets |
| `CompletedC3FinalReadoutKernelBridge` | Ledger/point-difference scalar readout | Normalization and boundary identities; not assumed to be a fixed linear functional of raw derivatives |

The closest existing **structured precursor** remains
`CanonicalC3BracketTfvdCompletionState M`. The closest existing **Hilbert
carrier** is `CanonicalCompletedC3FullWronskianOperatorCarrier`.
The construction uses its already defined four geometric sector vectors,
with canonical head cutoff `M = 1` and its exact tails. No tail is omitted.

## Exact carrier and fixed readout

Write `E = CanonicalCompletedC3FullWronskianOperatorCarrier` and
`Role = CanonicalCompletedC3StructuralChannel`.

```lean
abbrev CompletedPrimeDepthJetCarrier := WithLp 2 (Role → E)
primeDepthNormalizedResponseVectorJet : ℕ → CompletedPrimeDepthJetCarrier
primeDepthNormalizedResponseVectorReadout :
  CompletedPrimeDepthJetCarrier →L[ℂ] ℂ
```

All norms are the existing standard product/finite-family Hilbert norms.
No weight or metric is selected from moments.

Let `Q` be `canonicalC3ChartFactorHeight`, `F` be
`completedNativeOperatorCharacteristic`, and `S_role(z)` the existing raw
structural state. Define the single prescribed analytic normalizer

\[
d(z)=(Q(z)F(z))^{-1},\qquad V_{role}(z)=d(z)S_{role}(z).
\]

The fixed sector readout is the existing Wronskian contraction at the center:

\[
L(x)=(2\overline{F(0)})^{-1}
 \langle Q(0)^{-1}S_{full}(0),\;Jx\rangle.
\]

Here `J` is `canonicalCompletedC3FullWronskianOperator`, already constructed
upstream. The standard convention is conjugate-linear in the pinned first
argument and linear in `x`. The family readout is `ell(x) = sum_role L(x_role)`.
Neither `L` nor `ell` depends on the order. The scale is derived exactly from
the existing normalized response formula, not calibrated against a moment.

`primeDepthNormalizedStructuralState_readout` proves, before coefficients,
that this vector-sector synthesis is the existing normalized full response.
Its germ equals the prime-depth response by the two existing completed-response
identities.

## Normalization: triangular with a fixed germ

The normalization is nonlinear jointly in a varying source and denominator.
The theorem does **not** claim otherwise. Holding the prescribed canonical
normalizer fixed, the vector tower transform is linear:

\[
(T_N u)_r=\sum_{j=0}^{r}d_j u_{r-j},\qquad
 d_j=\frac{d^{(j)}(0)}{j!}.
\]

`completedPrimeDepthTaylorJet_smul` proves vector Leibniz with the exact
factorial normalization. `primeDepthNormalizedJetTransform_eq_jets` identifies
this finite linear transform with the actual normalized vector jets.
`primeDepthNormalizedJetTransform_prefix` proves cutoff coherence.

The all-order vector is

\[
(X_n)_{role}=\frac{V_{role}^{(2n+1)}(0)}{(2n+1)!}.
\]

`primeDepthNormalizedResponseVectorJet_eq_finiteTransform` identifies it with
the corresponding row of cutoff `2n+2`. Thus it includes all required raw
orders `0..2n+1`; it is not just a raw derivative with quotient declared linear.
The denominator, source vectors and readout are defined before mentioning
`primeDepthGeometricMoment` or canonical moments.

## Canaries and all-order closure

Source-first canaries:

- `primeDepthNormalizedResponseVectorJet_readout_zero`;
- `primeDepthNormalizedResponseVectorJet_readout_one`;
- `primeDepthNormalizedResponseVectorJet_readout_two`.

All-order capstone:
`primeDepthNormalizedResponseVectorJet_readout`:

\[
\ell(X_n)=(\operatorname{primeDepthGeometricMoment}(n):\mathbb C).
\]

The proof commutes the fixed sector continuous linear map with iterated
vector derivatives, synthesizes the finite labels, and uses equality of
response germs and the source-first reality theorem. It does not use
`primeDepthGeometricMoment_eq_canonical`.
Only the final corollary
`primeDepthNormalizedResponseVectorJet_readout_canonical` uses the earlier
uniqueness identification.

## Provenance and limits

- Head and exact tail stay in separate vector sectors until fixed synthesis.
- Archimedean completion and chart correction keep their existing separate
  trace sectors; neither is absorbed into fitted coefficients.
- These are existing completed trace projections, **not** a new lossless
  isometry of the entire structured TFVD/Green source.
- Analyticity of the complete carrier follows from its existing analytic
  spelling; tail analyticity follows from exact synthesis, not new tail bounds.
- No radial-normalized complex product-ledger jet is used. Reflected realified
  carriers are not silently treated as holomorphic.
- No moments, BR2, heights or Gram factor define any new vector or transform.
- The existing symplectic contraction is a fixed scalar readout, not an
  identification of variable-vector inner products with moments.
- The trace-family carrier is finite dimensional. No all-order linear
  independence or strict moment Gram is inferred from this lift.

BR2 may be tested downstream as an independence transport only, for the
correct final vector family and through a proved map.

## Single next gate

Identify a provenance-preserving geometric pairing/realization whose
variable-jet kernel satisfies

\[
\langle X_i,X_j\rangle\stackrel{?}{=}g_{i+j}.
\]

This is a question, not a theorem or an assumption here. The present fixed
readout theorem does not prove that the standard finite trace-family pairing
is the required all-order moment pairing; no such claim is made.

## Trust, validation and publication

Every public declaration is listed in
`PrimeDepthNormalizedResponseVectorJetAudit.lean`, audited with the existing
standard-three-axiom macro and `#print axioms`. A dependency-closure check
traverses types and proof bodies for all source declarations, excluding only
the final canonical-identification corollary, and rejects canonical moment,
Hankel, Jacobi/height and literal BR2 jet dependencies.

Required commands:

```bash
lake build --wfail CarrySelfAdjointOperator.PrimeDepthNormalizedResponseVectorJet
lake build --wfail CarrySelfAdjointOperator.PrimeDepthNormalizedResponseVectorJetAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

Validation completed:

- New source and focused audit: passed `--wfail` (9,276 jobs).
- Root and central audit: passed `--wfail` (9,707 jobs).
- `scripts/static_audit.sh`: `static audit passed`.
- `scripts/audit.sh`, including BR2/Order/recovered-C2 audits: `kernel audit passed`.
- All new public declarations have allowed axiom footprints only; the
  source/readout/triangular capstones print
  `[propext, Classical.choice, Quot.sound]`.
- Source-first transitive closure: 6,282 declarations checked.
- Placeholder/trust-escape scan and `git diff --check`: passed.

Publication is one coherent main commit, titled
`feat: lift normalized prime-depth response to geometric vector jets`,
containing the source, focused audit, root imports, declaration registry,
README and this report/checkpoint. Its exact hash is available in main's Git
history and the delivery report; no self-referential hash is inserted here.
No moment Gram or stronger downstream result is asserted.
