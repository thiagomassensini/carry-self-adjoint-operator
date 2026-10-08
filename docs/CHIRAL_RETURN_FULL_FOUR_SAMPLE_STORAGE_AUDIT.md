# Full four-sample chiral return storage — source-first closure

## Checkpoint and status

Initial main: `a8ee50ea268c3520b4e0bbec841ae628f5e13a55`.
`git pull --ff-only` was already up to date; initial HEAD/main/origin-main
matched and the working tree was clean. Only the llm main checkout is edited.

Statuses:

- `PASS_SOURCE_FIRST_FULL_FOUR_SAMPLE_STORAGE_POSITIVITY`.
- `PASS_FOUR_SAMPLE_UNIFORM_BOUNDARY_COERCIVITY`.
- `PASS_FULL_FOUR_SAMPLE_RETURN_CONTRACTIVITY`.

These are finite N=4 statements. The overall arbitrary-N gate remains
`PARTIAL_SOURCE_FIRST_CHIRAL_RETURN_STORAGE_POSITIVITY`. This report does
not close the global radial multiplier, a positive completed Green carrier,
all-order moment positivity, or spectral confinement.

## Reused source and metric

The source is exactly the existing completed characteristic F and its
companion -F', synthesized in `CanonicalCompletedNativeChiralCauchyCarrier`.
The existing identity `storage_one_eq_complete_slope_pairing` is reused,
with `q=-F'/F`, the unchanged radial nodes `I(i+1)/(k+1)`, and the same
source coefficient transformation F/P. Exact TFVD tails and completion
are those already incorporated in this source.

The raw integral-derived source coefficients and their mixed block signs
are reused from `CompletedNativeChiralReturnMixedSourceJets`. No canonical
moment or positivity consumer supplies them. The exact Taylor germ is

```text
-I q(I h) = sum_{j<4} (-1)^j c_j h^(2j+1) + h^8 R(h),
```

with R analytic at zero. The remainder is never removed or assigned a
pointwise positive sign.

## Complete boundary reconstruction

For `J_a(d)=sum_i d_i (i+1)^a`, a=0,1,2,3, the arithmetic inverse is fixed by
the four nodes, independently of every source or moment value:

```text
[  4   -13/3    3/2   -1/6 ]
[ -6    19/2   -4      1/2 ]
[  4    -7      7/2   -1/2 ]
[ -1    11/6   -1      1/6 ].
```

Both inverse identities are kernel-checked. The inverse was obtained by
exact arithmetic; Lean checks it against the original Euler boundary map.
It is a coordinate chart, not a new Hilbert metric or spectral operator.

Put `h=(k+1)^-1` and `x_a=h^a J_a(d)`. The normalized inverse reconstructs d
exactly at every nonzero h. All higher boundary coordinates are explicitly
retained: for m>=4 their regularized versions are sums of
`h^(m-a) * boundaryCoefficient(m,a) * x_a`, a<4. At h=0 those higher terms
vanish; they are not assumed zero at a finite radial step.

Similarly `Z_i(h,x)=h^3 d_i` is a polynomial in h,x. This removes the apparent
negative powers from the exact source remainder pairing.

## Exact full-source sewing

`radialFourSourceTemplate_synthesis` proves an equality of Cauchy vectors
before the mixed scalar readout:

```text
full source slope synthesis
 = synthesis of its own odd polynomial prefix
   + synthesis of its ENTIRE analytic remainder.
```

The template equals the actual completed source at all four radial nodes
with one common eventual cutoff. This follows from the existing Taylor
identity and the existing canonical grid, not interpolation or fitting.

The prefix energy is exactly the original all-order alternating Green
boundary expression evaluated on the regularized higher boundary jets.
The remainder energy keeps every ordered i/j cross, with the original
Cauchy denominator `(i+j+2)`:

```text
4 h Re sum_{i,j<4} conj(Z_i(h,x)) Z_j(h,x)
              (j+1)^8 R((j+1)h)/(i+j+2).
```

The factor h is exact: h^8 from the Taylor remainder, h^-6 from the two
reconstructed coefficient vectors, and h^-1 from the Cauchy metric.
Thus the entire full-source energy extends continuously to h=0. At zero
it equals exactly the positive four-coordinate boundary face already
proved from upstream integral certificates.

`storage_one_fourSample_eventually_regularized` is the complete scalar
sewing only AFTER both vector source channels have been synthesized.
No source vector is reconstructed from a scalar trace or moment target.

## Uniformity and quantitative bound

Continuity alone for each fixed x would not suffice. The proof uses the
compact unit sphere of the existing finite coefficient space to obtain
ONE neighborhood in h for EVERY unit x. The positive minimum of the
source-derived zero-step face supplies a uniform positive scalar margin.
It is a lower-bound constant, not a metric weight or fitted state amplitude.

Homogeneity is transported from the ORIGINAL full storage theorem
`chiralReturnStorage_smul`. Therefore the result applies jointly to all
coefficient vectors, including every mixed sector.

The previous exact finite seam is closed:

```text
exists epsilon > 0, eventually k, forall d : Fin 4 -> C,
 epsilon * sum_{a<4} normSq(h_k^a J_a(d))
 <= Re(storage k (radialCompletedInputCoefficients k d) 1).
```

Here `h_k=radialFourSourceStep k` is the real face of `canonicalGreenJetStep`.
The proof first bounds by the squared standard coefficient-chart norm and
then uses `sum_{a<4}|x_a|^2 <= 4 ||x||^2`. This ancillary finite norm is used
only for compactness and estimates; the Cauchy source inner product remains
unchanged.

Strict positivity holds for every nonzero d, with one eventual radial
threshold. The existing F/P coefficient change is invertible at the regular
samples, so the original chiral c family has the same strict sign.

Finally the existing `radialReturnTransfer_norm_le_one_iff_storage` gives
`eventually k, ||radialReturnTransfer k 4|| <= 1`. No new operator is defined.

## Scope and one next gate

No Hankel/Gram or positive Hilbert realization was constructed from target
data. No moment sign, HP certificate, Stieltjes, Jacobi/height or BR2 is an
input. Positivity of a local flux integrand is neither required nor proved.

The next finite gate is the analogous source-derived boundary-face sign
for N=5, involving the next raw source odd derivative and the enlarged even
block. The arbitrary-N route needs these face signs for every cutoff:
N=4 positivity cannot be promoted to all orders by induction without a
separate source reason. No such reason is assumed here.

## New public declarations

- `radialFourBoundaryInverseCoefficients`
- `radialFourBoundaryReconstruct`
- `radialFourBoundaryReconstruct_jets`
- `radialFourBoundaryReconstruct_source`
- `radialFourScaledBoundary`
- `radialFourNormalizedBoundaryInput`
- `radialFourScaledBoundary_input`
- `radialFourNormalizedBoundaryInput_scaled`
- `radialFourHigherBoundaryCoefficient`
- `radialFourRegularizedBoundary`
- `radialFourRegularizedInput`
- `radialFourRegularizedInput_eq`
- `radialFourRegularizedBoundary_eq`
- `radialFourRegularizedBoundary_zero`
- `radialFourRegularizedBoundaryEnergy`
- `radialFourRegularizedRemainderEnergy`
- `radialFourRegularizedStorage`
- `radialFourRegularizedStorage_zero`
- `radialFourRegularizedBoundary_continuous`
- `radialFourRegularizedInput_continuous`
- `radialFourRegularizedStorage_continuousAt`
- `radialFourRegularizedBoundary_smul`
- `radialFourRegularizedInput_smul`
- `radialFourRegularizedStorage_eventually_pos_on_unit`
- `radialFourRegularizedStorage_eventually_unit_margin`
- `radialFourSourceTemplate`
- `radialFourSourceTemplate_synthesis`
- `radialFourSourcePrefix_energy`
- `radialFourSourceRemainder_energy`
- `radialFourSourceTemplate_energy`
- `radialFourSourceStep`
- `canonicalGreenJetStep_eq_radialFourSourceStep`
- `radialFourSourceStep_pos`
- `radialFourSourceStep_tendsto_zero`
- `radialFourSourceTemplate_eventually_eq_slopes`
- `storage_one_fourSample_eventually_regularized`
- `radialFourNormalizedBoundaryInput_smul`
- `storage_one_fourSample_normalized_smul`
- `storage_one_fourSample_eventually_pos`
- `storage_one_original_fourSample_eventually_pos`
- `radialReturnTransfer_four_eventually_norm_le_one`
- `storage_one_fourSample_eventually_boundary_coercive`

## Trust, validation and files

The dedicated `CompletedNativeChiralReturnFourSampleStorageAudit` prints
axioms and checks all new declarations with `#assert_prime_depth_source_axioms`
and `#assert_oriented_green_source`. The latter traverses types and proof
values, rejecting canonical moments, HP/Stieltjes, Hankel, Jacobi/height,
Herglotz consumers and BR2. Allowed axioms are at most
`[propext, Classical.choice, Quot.sound]`.

Validation logs are preserved on llm at `/tmp/chiral-full-four-storage-validation/`.
Server Lean verification and GitHub Actions are reported separately.
All checks completed successfully on the llm main checkout:

```text
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnFourBoundaryReconstruction
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnFourSampleRegularization
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnFourSampleStorage
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnFourSampleStorageAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

All 42 new public declarations passed the axiom assertions. Their printed
footprints are subsets of `[propext, Classical.choice, Quot.sound]`.
The focused firewall checked 5,818 reachable declarations without a forbidden
source dependency. The new-file trust-escape/placeholder scan returned no
matches. Staged whitespace checks are repeated before each commit.
The broad root audits pass independently of the narrower source firewall:
their unrelated downstream declarations do not become premises here.

New files: the three source modules, dedicated audit and this report.
Updated: root imports, root Audit and README. No external repository or
Foundation file is edited. Main publication follows all checks; final
HEAD/main/origin-main/GitHub equality and clean tree are verified afterward.
