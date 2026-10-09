# Local material-clock center/leg observability audit

Date: 2026-10-09.

## Checkpoint and scope

Repository: `thiagomassensini/carry-self-adjoint-operator`, published `main`.
Initial HEAD = main = origin/main:
`fd8e04bf83557617c92c4def85da5daecb966887`.
`git pull --ff-only` reported already up to date. The tracked working tree was
clean. The two existing untracked files `C2OddTfvdTransport.lean` and
`C2OddTfvdTransportAudit.lean` are preserved, not staged or imported.

This formalizes the local material-clock proposal in the user attachment.
It does not reopen the all-order source, signed-pairing, boundary or height
capstones. It does not prove completed positivity. No positivity premise,
canonical moment values, metric fitting, BR2 or spectral data define the objects.

Statuses:

- `PASS_LOCAL_CENTER_LEG_CLOCK_OBSERVABILITY`.
- `PASS_ADJACENT_MATERIAL_LOG_GAP_DECOMPOSITION`.
- The existing completed chiral dominance / strict boundary sign remains open.

## Directed upstream audit

| Existing object | Role in this increment |
| --- | --- |
| `FiniteClockJets.finiteMaterialClock` / `finiteRealSpectralGenerator` | Existing diagonal generator on `FiniteRealSpectralHilbert M`; coordinate j means material integer j+1. Reused by a literal restriction theorem. |
| `realCpPairBracket` | Existing bracket at material center p(k+1), radius r. Reused to prove actual native source provenance. |
| `positiveLogGap`, `canonicalC3AdjacentClockChannels` | Existing adjacent material return, with both outer samples. Reused without changing its definition. |
| `NativeDepthCpLogJetCommutatorCrosswalk` | Existing vertical/horizontal coefficient crosswalk; it does not identify a tower vector with horizontal gradients. No such identification is used. |
| `CompletedNativeChiralReturnFiniteTransfer` | Existing finite completed return comparison. Not a source of a new sign theorem here. |
| `CompletedNativeChiralReturnGammaCorrectionCancellation` | Existing raw signed Gamma correction remains separate. Local observability supplies no bound on it. |
| `Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero` | Existing Mathlib Vandermonde zero-kernel theorem. This is the recovered argument, not a newly developed interpolation theory. |

The external mathematical API reused literally is Mathlib,
`Mathlib/LinearAlgebra/Vandermonde.lean`, with the named theorem above and its
existing determinant proof. The code records that provenance.

## Exact types and generator provenance

```lean
localMaterialLogClock {N : ℕ} (nodes : Fin N → ℕ) :
  (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)

materialBracketClockJet {N : ℕ}
    (nodes : Fin N → ℕ) (weights : Fin N → ℂ) :
  (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)
```

All carriers are existing finite coordinate spaces. No new norm is introduced.
For positive nodes bounded by M, `localMaterialLogClock_restriction` proves
exact equality with restricting `FiniteClockJets.finiteMaterialClock M` at
coordinates `nodes i - 1`.

With `ell_i = log(nodes i)` the observation is

$$
(Jf)_r=\sum_i w_i\ell_i^r f_i.
$$

`materialBracketClockJet_eq_clockPower` proves this is literally the bracket
applied to the r-th power of the restricted material generator. It is not
claimed to be an analytic response derivative: the dynamic generator's
`-i` factors, completion and normalization are separate layers.

`materialBracketClockJet_injective` assumes exactly: positive nodes, distinct
nodes, and nonzero bracket weights. Complex linearity is proved before recovery.
No Hilbert-product assertion is needed for this finite algebraic statement.

## Three-node theorem and native bracket

```lean
centerLegClockJet (c radius : ℕ) :
  (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)

centerLegClockJet_injective (c radius : ℕ)
    (hr : 0 < radius) (hc : radius < c) :
  Function.Injective (centerLegClockJet c radius)
```

The nodes are exactly `(c-radius,c,c+radius)`, with weights `(1,-2,1)`.
Clock orders 0,1,2 give the weighted Vandermonde from the attachment. Strict
monotonicity of the REAL logarithm on positive material nodes supplies the
frequency separation. No approximate logarithms enter the proof.

`centerLegClockJet_zero` proves the zeroth readout equals `f0 - 2*f1 + f2`.
`centerLegClockJet_nativeBracket` specializes the samples to
`realDirichletPower s` and proves equality with the EXISTING
`realCpPairBracket p radius k s` at `c=p(k+1)`.

The canary uses the single vector `(1,0,-1)`, independently of all moments:

$$
Bf=0,\qquad BLf=\log(c-r)-\log(c+r)
=\log\frac{c-r}{c+r}\ne0.
$$

Public canaries:

- `centerLegInvisibleSample_bracket`;
- `centerLegInvisibleSample_clock`;
- `centerLegInvisibleSample_clock_eq_logRatio`;
- `centerLegInvisibleSample_clock_ne_zero`.

## Arbitrary local block size, not arbitrary completed positivity

`cameraBlockMaterialNodes c h i = c-h+i` lists exactly `2h+1` material nodes.
The weights are `1` away from the central index h and `-2h` at h.

```lean
cameraBlockClockJet_injective (c h : ℕ)
    (hh : 0 < h) (hc : h < c) :
  Function.Injective (cameraBlockClockJet c h)
```

Orders `0,...,2h` recover every local coordinate. The condition `h>0` matters:
for h=0 the center weight is zero and the observation is not injective.
No dimension-uniform energy estimate or radial threshold is claimed.

`cameraBlockClockJet_zero_eq_radiusBrackets` certifies the weights BEFORE any
source specialization:

$$
(Jf)_0=\sum_{r=1}^{h}(f_{h-r}-2f_h+f_{h+r}).
$$

`cameraBlockClockJet_nativeRadiusSum` specializes the complete finite samples
and identifies this readout with the sum of the existing native Cp brackets
of radii `1,...,h` at center `p(k+1)`. Thus counts 3,5,7,9 are exact local
observability counts, not camera-spectrum multiplicities or height moments.

## Material masks

`localMaterialLogClock_mask` proves that multiplication by ANY specified
material-coordinate mask commutes with this diagonal generator. This covers
Haar/parity masks when they are actually presented at those material nodes.
It does not reinterpret a camera or a vertical depth as a material node,
and does not claim that brackets commute with the clock.

## Exact adjacent log-gap decomposition

Using the EXISTING `positiveLogGap`, write `d_n=log(n+2)-log(n+1)`. The module
`AdjacentMaterialLogGapDecomposition` proves

$$
d_n A-d_{n+1}B
=\frac{d_n+d_{n+1}}2(A-B)+\frac{d_n-d_{n+1}}2(A+B),
$$

and

$$
d_n-d_{n+1}
=\log\left(1+\frac1{(n+1)(n+3)}\right)>0.
$$

`canonicalC3AdjacentClockReturn_eq_symmetric_add_imbalance` applies this EXACTLY
to the two existing source products, for independent z,w:

$$
A=\nabla f_w(n+1)f_z(n),\qquad B=\nabla f_w(n)f_z(n+2).
$$

Both complex products remain present. The proof of positive real coefficient
is not a proof of a positive complex return amplitude or a nonnegative real
mixed orientation. No ordered cross or completion term is discarded.

## What this does not sew

The local generator is `log(material node)`. The existing completed
projective/chiral jet uses spectral/radial finite differences of a completed,
normalized source. They are not identified by matching jet labels.

The new results prove recoverability and an exact local coefficient
separation. They do not identify these finite observations with a positive
metric on the actual completed chiral/Gamma carrier. No new map, conditional
wrapper or fitted kernel is supplied to hide that missing transport.

The next research seam remains connecting this recoverable local material
information to the SAME completed chiral synthesis with tails, chart,
archimedean completion and residual retained, and proving its required sign.
Local injectivity alone cannot discharge the existing chiral dominance gate.
The preceding signed boundary transport and all its finite-step crosses and
analytic remainder remain unchanged.

## Public theorem inventory

`MaterialCenterLegClockObservability`:

1. `localMaterialLogClock_restriction`;
2. `localMaterialLogClock_mask`;
3. `materialBracketClockJet_eq_clockPower`;
4. `materialBracketClockJet_injective`;
5. `centerLegClockJet_injective`;
6. `centerLegClockJet_zero`;
7. `centerLegClockJet_nativeBracket`;
8. `centerLegInvisibleSample_bracket`;
9. `centerLegInvisibleSample_clock`;
10. `centerLegInvisibleSample_clock_eq_logRatio`;
11. `centerLegInvisibleSample_clock_ne_zero`;
12. `cameraBlockClockJet_zero`;
13. `cameraBlockClockJet_zero_eq_radiusBrackets`;
14. `cameraBlockClockJet_nativeRadiusSum`;
15. `cameraBlockClockJet_injective`.

`AdjacentMaterialLogGapDecomposition`:

1. `adjacentMaterialLogGap_decomposition`;
2. `adjacentMaterialLogGap_difference_eq`;
3. `adjacentMaterialLogGap_difference_re_pos`;
4. `canonicalC3AdjacentClockReturn_eq_symmetric_add_imbalance`.

## Trust and validation

The dedicated `MaterialCenterLegClockObservabilityAudit` registers every new
public theorem with `#assert_prime_depth_source_axioms`, prints the principal
capstones' axioms, and runs `#assert_oriented_green_source` on their complete
type/proof dependency closures. The latter rejects canonical moments,
HP/Stieltjes consumers, Hankel, spectral Jacobi/height, Herglotz and BR2.
The new combined closure passed with 2011 declarations.
Allowed footprint only: `[propext, Classical.choice, Quot.sound]` or a subset.
No new trust escape or assumed sign is added.

Commands run successfully:

```text
lake build --wfail CarrySelfAdjointOperator.MaterialCenterLegClockObservability CarrySelfAdjointOperator.AdjacentMaterialLogGapDecomposition
lake build --wfail CarrySelfAdjointOperator.MaterialCenterLegClockObservabilityAudit
lake env lean CarrySelfAdjointOperator/MaterialCenterLegClockObservabilityAudit.lean
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
git diff --cached --check
```

Complete compressed logs and readable tails are retained in
`research/material-center-leg-clock-2026-10-09/`. The local API-inspection
scratch file is not a theorem or a committed result. Final main publication
and remote equality are checked after commit/push. The tracked working tree
is clean at handoff; the two user-owned untracked files intentionally remain,
with their unchanged hashes recorded in the validation directory.

Files changed: the two proof modules, dedicated audit, root imports, README,
this report, and validation logs. Existing canonical objects and Foundation
files are unchanged.
