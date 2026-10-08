# Full six-sample ChiralReturn storage audit

## Checkpoint and scope

Initial audited `main`, after `git pull --ff-only`:
`8f56632c85e56c884d16cad7acd103a04d0784f2`.
HEAD, main and origin/main agreed. Two pre-existing untracked files,
`C2OddTfvdTransport.lean` and `C2OddTfvdTransportAudit.lean`, were present;
they are preserved and excluded from this work's commits.

Statuses:

- `PASS_SOURCE_FIRST_FULL_SIX_SAMPLE_STORAGE_POSITIVITY`
- `PASS_FULL_SIX_SAMPLE_RETURN_CONTRACTIVITY`

This is a **finite N=6 theorem**, not arbitrary-N or all-order positivity.
The previously proved raw theta-source sign and complete six-coordinate
boundary energy positivity are reused, not reproved.

## Geometric reconstruction and provenance

The original radial nodes are 1,...,6 and the existing radial step is
`radialFourSourceStep k = 1/(k+1)`. The name is reused because this is the
same grid, not a new scale. Euler boundary coordinates are
`b_a(d) = sum_i (i+1)^a d_i` and scaled coordinates are `x_a = h^a b_a(d)`.

`radialSixBoundaryInverseCoefficients` is the exact rational inverse of
this six-node Euler evaluation matrix. Both inverse identities are proved
in Lean. Its entries do not come from moments or a target Gram matrix.
`radialSixNormalizedBoundaryInput` reconstructs the original input from the
scaled coordinates when h is nonzero. Higher boundary coordinates remain
explicit finite linear combinations; none is discarded.

The existing actual-source expansion gives one analytic R near zero with
`-I*q(I*h) = sum_{j<6} (-1)^j c_j*h^(2j+1) + h^12*R(h)`.
Here q and c_j are the unchanged completed logarithmic source and its
source coefficients. The implementation reuses
`radialSixthOddSourceTemplate_eventually_eq_slopes` and the existing
source regularity theorem. No canonical moment equality is used to obtain
a sign or define the reconstruction.

## Complete synthesis before readout

`radialSixSourceTemplate_synthesis` retains the full vector prefix and its
order-twelve analytic remainder before applying the Cauchy mixed readout.
The exact identity `storage_one_sixSample_eventually_regularized` then
identifies original source storage with

`radialSixRegularizedStorage R h x = boundaryEnergy h x + remainderEnergy R h x`.

Every higher boundary coordinate and every one of the 36 Cauchy index
pairings remains present. The remainder is exactly

`4*h * Re(sum_{i,j<6} conj(D_h(x,i))*D_h(x,j)*(j+1)^12*R((j+1)*h)/(i+j+2))`,

where `D_h` is the polynomial regularized input. The factor h is derived
from h^12 in the source, h^-10 in the two reconstructed input factors and
h^-1 in the original Cauchy metric. This is not a bound obtained by deleting
cross terms. No pointwise sign of the remainder or flux is assumed.

At h=0 this full regularized storage equals the existing
`nativeSourceSixBoundaryEnergy x`. The even sector reuses
`nativeSourceFiveEvenBoundaryEnergy`; the odd sector is
`nativeSourceSixOddBoundaryEnergy`. Both sectors and all their terms are
retained.

## Uniform positivity and finite contractivity

Joint continuity at `(0,x)` follows from continuity of the actual analytic
R. The existing strict boundary positivity and compactness of the finite
unit sphere yield a single neighborhood of h=0 valid for **all** unit
vectors x. Homogeneity and invertibility of the geometric boundary chart
then give:

```lean
storage_one_original_sixSample_eventually_pos :
  ∀ᶠ k : ℕ in atTop, ∀ c : Fin 6 → ℂ,
    c ≠ 0 → 0 < (ChiralReturn.storage k c 1).re
```

The quantifier order is essential: one radial threshold works for all c.
The finite Pi norm is used only for compactness in a coordinate chart; no
source Hilbert metric is changed.

A quantitative version proves that some ε>0 works eventually for every d:

`ε * sum_{a<6} normSq(h_k^a*b_a(d)) ≤ Re(storage k (radialCompletedInputCoefficients k d) 1)`.

This is `storage_one_sixSample_eventually_boundary_coercive`. It does not
assert a fixed gap below one for the return operator norm as k tends to
infinity.

The existing exact equivalences yield:

- `radialReturnTransfer_six_eventually_norm_le_one`:
  eventually `norm(radialReturnTransfer k 6) ≤ 1`;
- `chiralMultiplier_six_eventually_contractive`:
  eventually `CanonicalCompletedNativeRadialChiralMultiplierContractiveAt k 6`.

The predicate takes arguments **k, N**. No arbitrary-N eventual contractivity
is claimed. Finite strict storage here does not establish strictness for a
future infinite completed carrier.

## Modules and capstones

New modules:

- `CompletedNativeChiralReturnSixBoundaryReconstruction`
- `CompletedNativeChiralReturnSixSampleRegularization`
- `CompletedNativeChiralReturnSixSampleStorage`
- `CompletedNativeChiralReturnSixSampleStorageAudit`

The root library and root Audit import the storage module and its dedicated
audit respectively. Public declarations are axiom-checked and printed in
the dedicated audit. The transitive oriented-source firewall checks 5839
declarations, rejecting the downstream HP/Stieltjes/moment-positivity,
Hankel/Jacobi/height and BR2 routes as proof sources. All reported axiom
footprints are subsets of `[propext, Classical.choice, Quot.sound]`.
No sorry, admit, new axiom, unsafe or trust escape is introduced.

## Validation

Passed focused commands:

```text
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnSixBoundaryReconstruction
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnSixSampleStorage CarrySelfAdjointOperator.CompletedNativeChiralReturnSixSampleStorageAudit
```

The final focused audit completed 9623 jobs. Relevant full transcripts are
retained on llm at `/tmp/six-reconstruction-build.log` and
`/tmp/six-full-focused-build.log`.

All repository-wide commands below passed. Their abbreviated validation transcript is recorded in `research/chiral-six-sample-storage-2026-10-08/validation.log`:

```text
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

## Frontier and files

The next finite candidate would require the N=7 source boundary sign and
its order-fourteen full analytic remainder transfer. No such result is
claimed here. Arbitrary-N source positivity remains a separate gate.
BR2 is not used as the source or as a positivity premise.

Modified existing files: `CarrySelfAdjointOperator.lean`,
`CarrySelfAdjointOperator/Audit.lean`, `README.md`.
New files: the four modules above, this report, and the validation/axiom logs.
Task changes are committed on main only after successful validation;
the two pre-existing untracked C2 files remain outside those commits.
