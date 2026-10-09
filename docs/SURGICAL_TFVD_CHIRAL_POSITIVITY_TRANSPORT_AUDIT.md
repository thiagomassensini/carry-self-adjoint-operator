# Surgical TFVD / chiral positivity-transport audit

## Checkpoints and result

Authoritative main after `git pull --ff-only`:
`77c07339da3051000f1848a8612439c73322a359`, equal to main/origin/main.
Initial tracked tree clean; the same two user untracked `C2OddTfvdTransport`
files are preserved and excluded from staging.

Historical map inspected read-only:
`teoria_dos_defeitos` checkout `/home/thlinux/Teoria_De_Defeitos`, commit
`898eceb` (not a dependency or normative Lean base), especially
`docs/NOTA_PONTE_ARQUIVOS_ANTIGOS_ROTA_POSITIVIDADE_TILT_DSLOPE_HANKEL_2026-08-31.md`.
The local supplied note and that repository copy have identical SHA-256:
`457875e89e0ba16ff37328e69e9c21933f64317712e01a8b81866a2ad16be7a8`.

New kernel result: `PASS_COMPLETE_CHIRAL_JET_BOUNDARY_TRANSPORT`.
Positivity result: `PARTIAL_JET_RESTRICTED_CHIRAL_DOMINANCE`.
No positivity, contractivity, nondegeneracy or new height theorem is claimed.

## 1. Directed inventory: what is actually proved

| Object / declaration | Exact role | What it does NOT supply |
|---|---|---|
| `carryTfvdCausalSecondDifference_inner_eq_bracket_add_trace` | For arbitrary `q : Real`, `x y : CarryVerticalL2`, inner of `q^-1 I - 2U + qU²` images equals bracket inner plus the two-trace metric | Not the inner product of the reconstructed source; not its spectral `dslope` |
| `carryTfvdMetricState_gram_posSemidef` | PSD of its own state in `WithLp 2 (CarryVerticalL2 × WithLp 2 (Complex × Complex))` | No identification of that analysis Gram with the completed logarithmic-response kernel |
| `canonicalC3CameraResolvedHolomorphicCentralInner_eq_tfvdFourChannel` | Original direct/reflected pairing after `G bracket + R trace`; GG, GR, RG, RR retained | Its pairing is distinct from the causal second-difference analysis metric |
| `canonicalC3BracketTfvdResponseTaylorCoefficient_eq_completed` | Every Taylor coefficient of the fully completed Wronskian response, independent of cutoff M | Scalar all-order transport is not a positive quadratic representation |
| `cameraFreeTfvdGreenPort_vector_intertwiner` | Actual port-valued function equality before scalar readout | No isometry with the completed moment kernel |
| `cameraFreeTfvdWronskianMoment_eq_canonical` | Exact scalar moment identity for each M and n | No Gram identity follows merely from this equality |
| `canonicalCompletedNativeGreenMomentGramDefect` | Desired parity kernel minus the actual product-ledger Taylor-jet inner product | Its vanishing is not proved; the forward-difference residual theorem takes a normalized Hilbert-kernel premise |
| `canonicalNativePolarizedTfvdGreenMomentKernelDefect_eq_ledger_total` | Explicit raw two-parameter residual = provenance + cross + readout residual + completion | It is a signed residual, not an additional positive norm |
| `coisometricFourChannelBalance_eq_rawGamma_add_gram_difference` | Complete source synthesis cancels three coisometric comparison channels as an exact Gram difference | Raw Gamma--Wronskian correction remains |
| `storage_re_eq_gammaEnergy_sub_rawGammaBalance` | Original source storage = `2*GammaEnergy - 2*Im(rawGammaBalance)` | No all-order one-sided inequality |
| `nativeSourceFiniteBoundaryEnergy_even_split` | Raw limiting face = four times the two source coefficient quadratics, with forced signs | Limiting mixed zeros do not remove finite-step mixed terms |
| `nativeSourceEvenBoundary_positive_iff_stieltjes` | Exact strict raw even-boundary gate for the old Stieltjes/height consumer | An iff is not a proof of that strict sign |

The exact spelling is **coisometric**, not `coisimetric`.

The raw `canonicalNativePolarizedTfvdGreenMomentKernelDefect M z w` uses
material Dirichlet parameters and `reflectedParameter z`. The Gamma defect
in section 3 instead uses the completed characteristic's spectral parameters
and the existing `operatorHeightParameter` crosswalk. They are NOT declared
equal by this audit. The completed corrected-ledger/source theorem already
supplies the appropriate dressing and chart/completion factors; no raw
material Green form is silently substituted for the spectral kernel.

The TFVD analysis map retains bracket/trace data and is injective for
`0<q<1`. However its metric is the norm of the causal second-difference
image. Reconstruction instead pairs `G bracket + R trace` in each argument,
including both mixed synthesis terms. The file
`CompletedNativeHolomorphicGreenTfvdFourChannel.lean` explicitly distinguishes
these two metrics. Preserving the state algebraically does not identify them.

## 2. Two parameters and the exact normalization

Use only the existing completed source:

\[
F=\texttt{completedNativeOperatorCharacteristic},\quad
C=-F',\quad a=C/(2F).
\]

For independent complex parameters the formal kernel is

\[
K(z,w)=\operatorname{dslope}(a)(\overline z,w),
\]

which on the real axis gives the requested divided difference, with the
existing derivative convention at collision. The division-free numerator is

\[
W(w,z)=C(w)\overline{F(z)}-F(w)\overline{C(z)}.
\]

The exact characteristic weight is
`canonicalCompletedC3GammaCharacteristicWeight z w = 2 * conj(F z) * F w`.
No factor is chosen to fit a coefficient. Away from zero denominators:

\[
W(w,z)=2\overline{F(z)}F(w)(w-\overline z)K(z,w).
\]

The code already proves this relation via the completed ledger numerator and
normalized-response cross identities. The argument order is W(w,z), with
Mathlib conjugate-linearity on the first Hilbert argument. The spectral
complex parameter, `operatorHeightParameter`, radial grid index k, internal
radius r and carry/depth index remain distinct. No height operator is used.

## 3. The first uncancelled geometric defect, already on main

Let Gamma(z) be `canonicalCompletedC3PolarizedGammaState z hz`, in
`CarryGammaComplexNaimark`, and set

\[
\Delta(z,w)=(w-\overline z)\langle\Gamma(z),\Gamma(w)\rangle-W(w,z).
\]

This is EXACTLY `canonicalCompletedC3RawGammaWronskianDefect z w hz hw`.
Its normalization is not implicit. Main already proves:

\[
(w-\overline z)\left[
 \langle\widehat\Gamma(z),\widehat\Gamma(w)\rangle-K(z,w)\right]
=\frac{\Delta(z,w)}{2\overline{F(z)}F(w)},
\quad
\widehat\Gamma(z)=\frac{\Gamma(z)}{\sqrt2 F(z)}.
\]

Exact declaration:
`canonicalCompletedC3Separation_mul_normalizedKernel_sub_dslope_eq_rawDefect_div_weight`.
The normalized Gamma Gram is unconditionally PSD **of its own source**.
The discrepancy above has no all-order dominance bound. Its vanishing would
be sufficient for exact kernel sewing, but is stronger than what positivity
needs; no zero-defect premise is introduced here.

On the actual fully synthesized radial source, define the existing weights
`alpha_i = c_i * r^(i+1) / positiveChiralCoordinate(z_i)`. The old balance is
literally

\[
B_{k,c,d,r,s}=\sum_{i,j}\overline{\alpha_i(c,r)}\alpha_j(d,s)
 \langle v_i,v_j\rangle\Delta(z_i,z_j).
\]

This is `ChiralReturn.rawGammaWronskianBalance`, with the original Cauchy
features, completed chiral coordinates, and every ordered cross. Main proves

\[
\Re S_k(c,r)=2\|\gammaSourceSynthesis(k,c,r)\|^2-2\Im B_{k,c,c,r,r}.
\]

The three coisometric corrections have already cancelled AFTER complete
synthesis. The one-sided bound on the displayed raw correction is not a
consequence of coisometry. Its two-sided Cauchy--Schwarz bound is insufficient.
No old theorem is reproved in this audit.

## 4. New minimal vector sewing: actual jets to the raw boundary

Reuse the old projective/chiral difference jets `Y_(p,k)` in
`CanonicalCompletedNativeProjectiveChiralCarrier`, literally a pair of the
same Cauchy Hilbert carrier. Their old definition is

\[
Y_{p,k}=\frac1{p!h_k^p}\sum_{r=0}^p(-1)^{p-r}\binom pr P_k(r),
\quad h_k=\texttt{canonicalCompletedC3RadialSecondStep }k.
\]

The source P is the EXISTING completed projective/chiral graph state. It uses
the completed F,C and intrinsic chiral amplitude; those traces come from the
completed TFVD synthesis, with tails, Xi and chart correction already included.
This does not assert a lossless inverse from the traces to every structured
Green-port coordinate. No new such inverse or Hilbert carrier is built.

Only synthesize the already-existing vectors:

\[
J_{n,k}(x)=\sum_{i<n}(-1)^ix_{2i}Y_{2i,k}
 +\sum_{i<n}(-1)^ix_{2i+1}Y_{2i+1,k}.
\]

The signs are exactly the old raw-boundary phases. Neither g nor h is used
to define J. The old signed form remains
`B(u,v)=1/2*(inner u.1 v.1 - inner u.2 v.2)`.

New kernel-checked results, for arbitrary n and independent x,y:

1. `nativeSourceProjectiveBoundaryJetSynthesis_pairing`: the FULL signed
   pairing equals its double coefficient sum, including every even/odd mixed
   finite-step cross. No finite mixed orthogonality is assumed.
2. `nativeSourceProjectiveBoundaryJetSynthesis_pairing_tendsto`: that pairing
   tends to the two polarized source coefficient blocks. Existing mixed
   coefficients become zero only at the proved limit.
3. `nativeSourceProjectiveBoundaryJetSynthesis_energy`: after complete
   synthesis, `4*Re B(J,J)=2*(norm(J.1)^2-norm(J.2)^2)`.
4. `nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto`: EXACTLY

\[
2(\|J_{n,k}(x)_+\|^2-\|J_{n,k}(x)_-\|^2)\longrightarrow E_{2n}(x).
\]

This is a concrete whole-vector transport identity with no sign premise,
not a tautological positive-assumption wrapper. The all-order coefficient
limit is the existing projective/chiral result, and its scalar uniqueness
identification is used only after the vectors have been defined.

The old canaries have indices (0,0)->g0, (0,1)->0, (1,1)->g1; the literal
(2,2) jet reads g2. No index-sum is guessed. The new whole-source result agrees
with the raw coefficient normalization certified in the earlier N<=7 work:
`c_j=2g_j`, and the outer boundary scale is four. It does not extrapolate the
N=7 strict margin or compute a new N=8 certificate.

## 5. The minimum sign question: restrict to each jet sector

The signed source/kernel identification in section 4 is now closed. The first
open obligation on THIS route is **2: dominance of two forms** on the actual
finite jet syntheses. An identification with an unrelated positive Gram is
not needed, and no global Cauchy-space operator contraction is required.

For the semidefinite side it is sufficient to bound the two pure jet sectors,
for instance the following statement (NOT a theorem or new assumption
installed in Lean):

```lean
∀ n : ℕ, ∀ u : Fin n → ℂ, ∀ᶠ k : ℕ in Filter.atTop,
  let Je := nativeSourceProjectiveBoundaryJetSynthesis n k
    (nativeSourceBoundaryFromParity n u 0)
  let Jo := nativeSourceProjectiveBoundaryJetSynthesis n k
    (nativeSourceBoundaryFromParity n 0 u)
  ‖Je.2‖^2 ≤ ‖Je.1‖^2 ∧ ‖Jo.2‖^2 ≤ ‖Jo.1‖^2
```

Here the threshold may depend on n AND u. This pointwise eventual statement
is enough for each limiting quadratic to be nonnegative. It neither asserts
full finite-step mixed-sector positivity nor deletes any crosses. The new
public pairing theorem still retains them all.

The exact kernel formulas above also permit a weaker direct bound on the
normalized Gamma defect **in these synthesized directions**, instead of
forcing Delta=0. No existing source-correct bound of that kind was found.

**3: nondegeneracy remains a separate strictness issue after PSD.** Even strict
inequalities at every finite k can tend to zero. Therefore a positive
nonvanishing LIMIT gap is necessary for the strict Stieltjes gate. No claim
that mere finite strict contractivity supplies `PosDef` is made. The existing
`nativeSourceEvenBoundary_positive_iff_stieltjes` and old height handoff
remain consumers; they are not invoked with a fabricated sign proof.

**1: source/port identity** is still absent if one insists on the OLD positive
TFVD analysis metric or old cumulant return as the witness. The completed
traces/response equality cannot supply that metric morphism. It is not an
extra missing source equality for the direct signed-jet route just proved.

## 6. Historic cumulative / Naimark route and incompatibility tests

The cited historical note labels the identification of its unitary colligation
with current chiral transport as an inference, not a proved crosswalk.
`I-C* C = D* D` applies only after that same-source colligation is supplied.

`DEFEITO_GREEN_CUMULANTES_MELLIN.md` defines the dressed equation
`Psi=A B=Euler(A)`. Main has its formal scalar algebra in `MultiplicativeValve`:
`IsTowerChannel`, `IsLogDerivChannel` (`B*A=X*A'`), uniqueness and product rules.
The prime-depth moment recurrence is already closed. These coefficient
identities do not turn their triangular transform into an isometry or a
contraction on the normalized Wronskian jets.

The historical local `A_m` averages prime-power coordinates into prime slots,
with `A_m A_m*=I` and log-generator intertwining. It is not the scalar mass A
in `Psi=A B`. Its source labels, inner product and parameter space differ from
the present two-chirality Cauchy jets. The scripts are numerical/architectural
records, not imported Lean theorems. The global-candidate script explicitly
reports a Green residual when local blocks are stacked.

The same document later distinguishes a reduced rational-frequency problem
from a stronger pairwise problem, with different finite numerical feasibility
and norm bounds. Neither numerical outcome proves the present all-order
jet-sector inequality. Aggregating equal rational frequencies is not permission
to discard independent spectral-parameter crosses. No optimizer, polar
isometry, target-fit or old numeric coefficient enters this module.

The old concrete C3 positive state is kept refuted. Its documented bound is
`h0 < 1/16 < K_C3(0,0)`, obtained from
`canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth` and
`infiniteReflectedGreenEnergy_half_gt_sixteenth`, retaining the extra positive
log-jet/residual terms. These are diagnostics, not sign premises for J.
Main proves its central
dressed defect is strictly positive and the corresponding sewing residual
strictly negative (`CompletedC3KernelMetricCalibration` and
`CompletedC3ConcretePositiveSewingClosure`). An isometry preserves that mismatch.
The new J uses the ALREADY-PROVED signed projective/chiral state, including the
Cauchy separation and two intrinsic chiral channels; it is not a rescaled
literal C3 Gram. No positive Gram identification is asserted for J.

## 7. Dependency and validation record

New module: `CompletedNativeChiralBoundaryJetTransport.lean`.
New dedicated audit: `CompletedNativeChiralBoundaryJetTransportAudit.lean`.
Five new public declarations are enforced/printed there: the synthesis
function and the four theorems listed above.

The source-only dependency checker covers the vector definition and finite
identities (5218 reachable declarations). The limit checker excludes
HP/positive Stieltjes consumers, Hankel, Jacobi/height, Herglotz and BR2
(5599 reachable declarations). Scalar canonical coefficient identification
at the existing final uniqueness step is permitted; positive downstream
hypotheses are not. Trust footprint at most
`[propext, Classical.choice, Quot.sound]`.

No BR2 source, new metric, Gram fitted from moments, carrier, operator,
contraction hypothesis or new sign certificate is added.
Validation results and preserved logs are recorded after execution below.


### Executed validation — 2026-10-09

All exited zero on the authoritative llm checkout:

- `lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralBoundaryJetTransport CarrySelfAdjointOperator.CompletedNativeChiralBoundaryJetTransportAudit`;
- `lake env lean CarrySelfAdjointOperator/CompletedNativeChiralBoundaryJetTransportAudit.lean`;
- `lake build --wfail CarrySelfAdjointOperator`;
- `lake build --wfail CarrySelfAdjointOperator.Audit`;
- `bash scripts/static_audit.sh`;
- `bash scripts/audit.sh`, ending with `kernel audit passed`;
- `git diff --check`, followed by staged diff checking before publication.

Capstone footprint: `[propext, Classical.choice, Quot.sound]` only.
Full logs and readable tails:
`research/chiral-surgical-jet-transport-2026-10-09/`.
README is appended with the signed transport and the open dominance/strictness
frontier. The two user untracked files remain identical by SHA-256.

No full-state equality, positive Gram, PSD, PD, contraction or new height
closure is inferred from a type check or from this signed limit identity.
The old height consumer is left ready to receive the actual strict boundary
sign when that sign is proved.
