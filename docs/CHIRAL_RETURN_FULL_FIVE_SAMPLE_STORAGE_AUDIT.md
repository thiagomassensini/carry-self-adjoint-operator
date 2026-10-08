# Full five-sample chiral source storage

## Checkpoint and scope

- Repository: `thiagomassensini/carry-self-adjoint-operator`, exclusively `main`.
- Initial verified `HEAD = main = origin/main`: `76a08cb87ee5f055f80924a48fd979271ec0cbf9`.
- `git pull --ff-only` was already up to date; the initial working tree was clean.
- Status: **PASS_SOURCE_FIRST_FULL_FIVE_SAMPLE_STORAGE_POSITIVITY**.
- Consequence: **PASS_FULL_FIVE_SAMPLE_RETURN_CONTRACTIVITY**.

This transfers the previously proved positive five-coordinate boundary face
to the **full** original radial storage at N=5. It does not infer arbitrary-N
positivity, global Pick/Herglotz positivity, or canonical Hankel strictness.
The published `main` remains the normative formal checkpoint.

## Existing source reused

The unchanged completed source is `completedNativeOperatorLogDerivative`.
`nativeSourceTransverseSlope_five_exact_remainder` already provides an
analytic R at zero with

```text
-I q(I h) = sum_{j<5} (-1)^j c_j h^(2j+1) + h^10 R(h),
c_j = nativeSourceOddBoundaryCoefficient j.
```

`radialFifthOddSourceTemplate_synthesis` already synthesizes this ENTIRE
prefix and remainder in the original Cauchy carrier, for any finite node
family, before any mixed readout. It is reused, not reproved. The new real-step
adapter `radialFiveSourceTemplate` is exactly that existing template at the
five original nodes. The canonical radial grid and its real face
`radialFourSourceStep k = 1/(k+1)` are also reused unchanged.

The previously certified `nativeSourceFiveBoundaryEnergy_pos` supplies the
boundary sign from the original raw theta/Xi integrals. No new quadrature,
canonical moment sign, HP/Stieltjes certificate, Hankel, spectral Jacobi,
height, BR2 source, fitted coefficient or new metric is introduced.

## Complete geometric boundary chart

For d : Fin 5 -> C, set

```text
x_a = h^a sum_{i:Fin 5} (i+1)^a d_i,  a=0,...,4.
```

The arithmetic inverse is fixed solely by the nodes 1,2,3,4,5:

```text
[  5   -77/12   71/24   -7/12    1/24 ]
[ -10  107/6   -59/6    13/6    -1/6  ]
[  10  -39/2    49/4     -3      1/4  ]
[  -5   61/6   -41/6    11/6    -1/6  ]
[   1  -25/12   35/24   -5/12    1/24 ].
```

Lean proves both inverse identities, for every complex coefficient vector.
The scaled inverse is valid at every nonzero h. Higher Euler boundary jets
are reconstructed by the SAME inverse; none is discarded. Their continuous
regularization is `h^m * radialEulerBoundaryJet d m`. At h=0 only the first
five coordinates survive, giving exactly `nativeSourceFiveBoundaryExtension`.

The full coefficient vector is regularized as `h^4 d`. This is a reversible
coordinate chart at nonzero h, not a different Cauchy inner product or an
extra weight chosen for positivity.

## Exact remainder and cross terms

The regularized prefix energy is the existing alternating Green boundary
identity summed through j=4, including higher boundary orders through 8.
The exact remainder energy is

```text
4 h Re sum_{i,j:Fin 5}
  conj((h^4 d)_i) (h^4 d)_j (j+1)^10 R((j+1)h)/(i+j+2).
```

All 25 crosses remain. The factor h follows exactly from h^10 in the source,
h^-8 in the two input factors, and h^-1 in the Cauchy feature kernel.
No sign of an individual remainder term or local flux is assumed.

`radialFiveSourceTemplate_energy` proves the exact equality only AFTER the
complete vector synthesis. With the existing source regularity and exact
Taylor theorem, `storage_one_fiveSample_eventually_regularized` identifies
this regularized expression with the actual storage for all five-coordinate
inputs, under ONE eventual radial threshold.

## Uniform sign and coercivity

The full regularized expression is jointly continuous at `(h,x)=(0,x)`.
At h=0 it equals the already strictly positive five-coordinate source face.
Compactness of the finite coefficient unit sphere supplies ONE positive
margin and ONE neighborhood for ALL unit vectors. Homogeneity and the exact
inverse chart then transfer the sign to all nonzero original inputs.

The unit sphere uses the existing Pi coefficient norm solely for compactness
and normalization. It does not replace the original Cauchy carrier metric.

Main capstones:

```lean
storage_one_fiveSample_eventually_pos :
  ∀ᶠ k in atTop, ∀ d : Fin 5 → ℂ, d ≠ 0 →
    0 < (ChiralReturn.storage k (radialCompletedInputCoefficients k d) 1).re

storage_one_original_fiveSample_eventually_pos :
  ∀ᶠ k in atTop, ∀ c : Fin 5 → ℂ, c ≠ 0 →
    0 < (ChiralReturn.storage k c 1).re

radialReturnTransfer_five_eventually_norm_le_one :
  ∀ᶠ k in atTop, ‖radialReturnTransfer k 5‖ ≤ 1
```

`storage_one_fiveSample_eventually_boundary_coercive` further proves

```text
exists epsilon > 0, eventually k, for every d,
  epsilon * sum_{a:Fin 5} normSq(x_a)
    <= Re(storage k (radialCompletedInputCoefficients k d) 1).
```

Its finite-dimensional constant comes from the source face's compact unit
margin and the elementary inequality sum normSq(x_a) <= 5 norm(x)^2.
Contractivity is obtained with the EXISTING
`radialReturnTransfer_norm_le_one_iff_storage`, not a new operator.

## Remaining frontier

The open obligation is still the source-derived sign of the corresponding
complete Green boundary face for arbitrary N, followed by its exact
remainder transfer. N=6 is the next finite boundary test; the present proof
uses only the certified face at N=5 and cannot establish all-order positivity.
No new Hilbert realization of the entire moment kernel is claimed.

## Files and provenance audit

New modules:

- `CompletedNativeChiralReturnFiveBoundaryReconstruction.lean`;
- `CompletedNativeChiralReturnFiveSampleRegularization.lean`;
- `CompletedNativeChiralReturnFiveSampleStorage.lean`;
- `CompletedNativeChiralReturnFiveSampleStorageAudit.lean`.

The root and root Audit import the new gate. README adds the new checkpoint
without deleting the older boundary-only and presentation-obstruction history.
No old source definition, carrier, scalar readout, metric or audit firewall
is changed.

The dedicated audit checks all 38 public declarations with
`#assert_prime_depth_source_axioms`, `#print axioms`, and the transitive
`#assert_oriented_green_source`. The dependency traversal covers 5,830
declarations. Every footprint is within `[propext, Classical.choice, Quot.sound]`.
The existing narrow classical-theta audit exceptions are unchanged; forbidden
canonical targets, HP/Stieltjes, Hankel, spectral Jacobi/height and BR2
remain excluded from the new source proofs.

Validation commands, executed on llm with Lean v4.32.0:

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnFiveSampleRegularization
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnFiveSampleStorage
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnFiveSampleStorageAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

The focused and full builds, source/axiom audit, both audit scripts and
whitespace checks passed. The final validation outcomes are recorded below. Detailed logs
are preserved on llm in `/tmp/chiral-five-full-storage-validation/`.
Commit and push occur only after builds, audits and staged whitespace checks
pass; the final published refs and clean-tree check are reported separately.

## Final validation outcome

All displayed commands passed on llm with Lean v4.32.0. The dedicated
audit checked all 38 public declarations and 5,830 transitive dependencies.
No audit firewall was changed. The compact validation log is tracked at
`research/chiral-five-full-storage-2026-10-08/validation.txt`; detailed logs
remain in `/tmp/chiral-five-full-storage-validation/`.

The radial node multipliers are Euler chart coordinates, not material time,
C2 depth or a height parameter. The result is confined to the original
N=5 sample family. Final clean-tree and published-ref equality are checked
after commit/push and stated in the delivery report.
