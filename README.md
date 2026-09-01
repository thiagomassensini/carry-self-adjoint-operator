# Carry Self-Adjoint Operator

Lean 4 formalization of a native-carry construction of finite and completed
signed-height operators. The operator is derived from the completed native
characteristic and its logarithmic moments. It does **not** accept a zero
table, target heights, a fitted Jacobi matrix, or a scanned spectral parameter
as input.

## Two Routes, One Construction

This repository contains two related routes. They meet at the moment kernel,
but they are not the same proof.

| Route | Purpose | Output |
|---|---|---|
| **Height-operator route** | Derive the Jacobi and signed-height operators from the native characteristic and explicit certificates | Symmetric finite operators and maximal self-adjoint completed constructions |
| **Green/Gram route** | Relate the same moments to a positive Hilbert kernel | PSD/PD implications and the independence data consumed by the operator route |

```mermaid
flowchart LR
  subgraph HEIGHT["A. Height-operator construction"]
    L["native log evolution"] --> F["completed characteristic F"]
    F --> R["response R = -F' / (2F)"]
    R --> M["canonical moments h_n"]
    M --> HK["Hankel pair G_N and K_N"]
    HK --> J["Jacobi section J_N"]
    J --> T["height operator T_N = J_N^(-1/2)"]
    T --> S["signed operator H_N = T_N ⊕ (-T_N)"]
    S --> I["completed maximal self-adjoint operator"]
  end

  subgraph GREEN["B. Green/Gram certification"]
    B["carry bracket"] --> V["enriched TFVD carrier"]
    V --> GP["Green boundary port"]
    GP --> C3["completed C3 ledger"]
    C3 --> D["total dslope kernel"]
    D --> GR["Hilbert Gram realization"]
    GR --> P["PSD/PD plus parity independence"]
  end

  D -. "same moments" .-> M
  P -. "positivity certificate" .-> HK
```

## The Exact Meeting Point

Let

$$
F(z)=\texttt{completedNativeOperatorCharacteristic}(z),
\qquad
R(z)=\frac{-F'(z)}{2F(z)}.
$$

The completed C3 ledger keeps its channels separate until the final readout:

$$
\mathcal L_M=
(\text{radial},\text{provenance},\text{off-diagonal},\text{residual},
\text{tail},\xi,\text{chart}).
$$

After that final readout, and only then, the nonzero chart,
characteristic, and separation factors are normalized. On the real height
axis the resulting total kernel is

$$
\mathcal K_M(x,z)
=\operatorname{dslope}R(x,z)
=
\begin{cases}
\dfrac{R(z)-R(x)}{z-x}, & x\ne z,\\[6pt]
R'(x), & x=z.
\end{cases}
$$

Whenever `F(x)` and `F(z)` are nonzero, the identity is exact at every
cutoff:

$$
\mathcal K_M(x,z)=\mathcal K_N(x,z)
\qquad\text{for all }M,N.
$$

Its mixed forward differences converge to the canonical polarized moments in
all four even/odd blocks. This is formalized in
[`CompletedC3FinalReadoutKernelBridge.lean`](CarrySelfAdjointOperator/CompletedC3FinalReadoutKernelBridge.lean):

- `canonicalCompletedC3AllCutoffOffDiagonalKernelReadout_eq`;
- `canonicalCompletedC3AllCutoffRealKernelReadout_eq_dslope`;
- `canonicalCompletedC3AllCutoffRealKernelReadout_cutoff_independent`;
- `canonicalCompletedC3AllCutoffRealAxisKernelForwardDifference_tendsto_moment`;
- `canonicalCompletedC3AllCutoffRealAxisKernelParityForwardDifference_tendsto`.

> **Logical guardrail:** the theorem above proves
> `completed ledger -> dslope kernel -> moments`. It does not silently replace
> the scalar readout by a positive inner product. Positivity uses the separate
> identity `K(x,z) = <Phi(x), Phi(z)>` with an actual Hilbert-valued state
> `Phi`.

That distinction prevents the scalar Green/Wronskian sewing from being
confused with the Gram-positivity certificate used to construct the Jacobi
operator.

| Formal statement | Lean status |
|---|---|
| Native characteristic determines one real moment sequence | Proved by recurrence and uniqueness |
| Completed C3 final readout gives the total `dslope` kernel | Proved, cutoff-independent |
| Mixed kernel differences give all four moment blocks | Proved by an all-order limit |
| Hilbert realization of that kernel implies Hankel PSD | Proved as a representation theorem |
| Prefix independence upgrades PSD to PD | Proved for the even and odd families |
| Scalar readout alone is a positive Gram | Deliberately not asserted |

At the Lean type level, Route A consumes explicit arguments such as
`IsShiftedMomentGramRepresentation`, `Matrix.PosDef`, and
`LinearIndependent`. Route B is responsible for constructing or transporting
those certificates. This boundary separates the derivation of the height
operator from the proof that its canonical moment matrices are positive.

## Route A: Height Operator

### 1. Native characteristic

The starting operator is the maximal self-adjoint logarithmic generator,
with its exact basis law formalized by
`nativeLogGenerator_isSelfAdjoint` and
`nativeLogGenerator_basisVector_log` in
[`NativeLogEvolution.lean`](CarrySelfAdjointOperator/NativeLogEvolution.lean).

The exact head-plus-tail camera characteristic is cutoff-independent. After
removing the camera chart and applying the completion factor, the common
scalar is

$$
F(z)=\texttt{nativeXiCompletionFactor}(z)\,
     \texttt{nativeHeightScalar}(z).
$$

The camera-independent definition and its cross-multiplied camera bridge are
in
[`CompletedOperatorCharacteristic.lean`](CarrySelfAdjointOperator/CompletedOperatorCharacteristic.lean).
No division by a camera factor is used in that bridge.

### 2. Canonical logarithmic moments

Write the even characteristic in its real Taylor coordinate as

$$
\Phi(u)=\sum_{n\ge 0}a_n u^n,
\qquad a_0\ne0.
$$

The moments are defined recursively by the division-free logarithmic
derivative identity

$$
a_0h_n+
\sum_{k=0}^{n-1}h_k a_{n-k}
=-(n+1)a_{n+1}.
$$

This produces a unique real sequence

$$
h_n=\texttt{canonicalCompletedNativeLogDerivativeMoment}(n).
$$

The definition, recurrence, existence, and uniqueness are in
[`CompletedNativeRealWeylMoments.lean`](CarrySelfAdjointOperator/CompletedNativeRealWeylMoments.lean),
notably:

- `canonicalCompletedNativeLogDerivativeMoment_isMomentSequence`;
- `completedNativeLogDerivativeMoment_eq_canonical`.

### 3. Hankel pair and canonical whitening

For each finite order `N`, the two moment sections are

$$
G_N(i,j)=h_{i+j},
\qquad
K_N(i,j)=h_{i+j+1}.
$$

The normalized LDL decomposition of `G_N` fixes the whitening factor
canonically:

$$
B_NG_NB_N^{\mathsf T}=I.
$$

The Jacobi section is then

$$
J_N=B_NK_NB_N^{\mathsf T}.
$$

The definitions and exact whitening laws are in
[`CanonicalLDLWhitening.lean`](CarrySelfAdjointOperator/CanonicalLDLWhitening.lean)
and
[`CanonicalFiniteHeight.lean`](CarrySelfAdjointOperator/CanonicalFiniteHeight.lean).
The positivity and independence arguments are explicit parameters here; no
fitted matrix is hidden in the definition.

### 4. Positive and signed heights

Functional calculus gives

$$
T_N=J_N^{-1/2},
\qquad
H_N=T_N\oplus(-T_N).
$$

Lean proves exact symmetry and the finite spectral readout:

- `canonicalFiniteHeightOperator_isSymm`;
- `canonicalFiniteHeightOperator_charpoly`;
- `canonicalSignedFiniteHeightOperator_isSymm`;
- `canonicalSignedFiniteHeightOperator_charpoly`;
- `signedSectorReflection_conj_canonicalSignedFiniteHeightOperator`.

See
[`CanonicalFiniteHeight.lean`](CarrySelfAdjointOperator/CanonicalFiniteHeight.lean)
and
[`SignedFiniteHeightOperator.lean`](CarrySelfAdjointOperator/SignedFiniteHeightOperator.lean).

### 5. Completed operator

The compatible Green-jet tower is promoted to closed even and odd Hilbert
sectors. The closed energy factor produces

$$
J=B^*B,
$$

and the reciprocal signed block realizes the completed height operator. The
reduced construction does not require the separate zero-mass/head-tail
closure field.

The principal self-adjointness statements are:

- `closedGreenJetReducedReciprocalSignedHeightOperator_adjoint_eq`;
- `canonicalCompletedGreenJetReducedReciprocalSignedHeightOperator_adjoint_eq`;
- `heightOperator_adjoint_eq`;
- `reducedHeightOperator_adjoint_eq`.

They are formalized in
[`GreenJetReciprocalSignedHeightOperator.lean`](CarrySelfAdjointOperator/GreenJetReciprocalSignedHeightOperator.lean)
and
[`CompletedNativeGreenWeylHeight.lean`](CarrySelfAdjointOperator/CompletedNativeGreenWeylHeight.lean).
The corresponding certificate types expose their moment, Gram, parity, and
closure inputs rather than hiding them as global assumptions.

The complexified reduced operator has real point eigenvalues by
`complexifiedReducedHeightOperator_eigenvalue_im_eq_zero` in
[`CompletedNativeJacobiWeylContinuation.lean`](CarrySelfAdjointOperator/CompletedNativeJacobiWeylContinuation.lean).

## Route B: Green and Gram Positivity

### 1. Geometry to TFVD and Green

The geometric route is retained before scalarization:

$$
\text{center/legs}
\longrightarrow\text{causal bracket}
\longrightarrow\text{enriched TFVD state}
\longrightarrow\text{Green boundary port}.
$$

The completed source stores value, log-jet, exact tails, provenance, and the
Green port in one state. The four completed scalar traces are identified with

$$
(F(z),-F'(z),F(w),-F'(w)),
$$

while the Green side remains in its direct, reflected, and quarter-turned
Naimark coordinates. See:

- [`CompletedC3FourTraceSymplecticBridge.lean`](CarrySelfAdjointOperator/CompletedC3FourTraceSymplecticBridge.lean);
- [`CompletedC3EnrichedSymplecticNoLeakBridge.lean`](CarrySelfAdjointOperator/CompletedC3EnrichedSymplecticNoLeakBridge.lean);
- [`CompletedC3BracketTfvdGreenFactorization.lean`](CarrySelfAdjointOperator/CompletedC3BracketTfvdGreenFactorization.lean).

The final readout reconstructs the completed Wronskian of `(F,-F')` exactly,
but no structural channel is declared zero in that identity.

### 2. Scalar kernel to finite moments

The new completed bridge proves

$$
\text{C3 final readout}
\longrightarrow \operatorname{dslope}R
\longrightarrow \bigl(h_{i+j}\bigr)_{i,j}
\quad\text{and}\quad
\bigl(h_{i+j+1}\bigr)_{i,j}.
$$

This part is cutoff-independent and does not use a list of spectral heights.

### 3. Gram certification

If the same real-axis kernel is realized by a Hilbert state,

$$
\operatorname{dslope}R(x,z)
=\langle\Phi(x),\Phi(z)\rangle,
$$

then its finite forward differences are honest Gram matrices. Entrywise
limits therefore give

$$
G_N\succeq0,
\qquad
K_N\succeq0.
$$

Linear independence of the even and odd feature prefixes upgrades these to
strict positivity. The relevant interfaces and implications are in:

- [`CompletedGreenForwardDifferenceGramBridge.lean`](CarrySelfAdjointOperator/CompletedGreenForwardDifferenceGramBridge.lean);
- [`GreenKernelCoefficientClosure.lean`](CarrySelfAdjointOperator/GreenKernelCoefficientClosure.lean);
- [`BR2IncidenceStrictPositivity.lean`](CarrySelfAdjointOperator/BR2IncidenceStrictPositivity.lean);
- [`CurrentInfiniteHeightStatus.lean`](CarrySelfAdjointOperator/CurrentInfiniteHeightStatus.lean).

In particular, `BR2BracketIncidenceJetTransport` is all-order: its even and
odd identities are indexed by every `n : Nat`, and injectivity transports the
global bracket-incidence independence to the complete Green-jet families.

### 4. Fixed-parameter causal contraction audit

The proposed factorization of every causal source through one fixed positive
Wronskian readout is ruled out, rather than assumed. The positive trace has
real dimension `12`, while thirteen explicit completed C3 symplectic camera
states are real-linearly independent. Hence both the fixed-parameter kernel
compatibility and its defect-Gram contraction fail throughout the open upper
half-plane. This audit is proved in
[`CompletedC3CausalChiralKernelObstruction.lean`](CarrySelfAdjointOperator/CompletedC3CausalChiralKernelObstruction.lean)
using Dedekind independence of the underlying Dirichlet characters and the
existing global camera isometry; it uses no zero or spectral premise.

## What Is Not Being Identified

The following objects are deliberately distinct in the formalization:

| Object | Type of information |
|---|---|
| Completed C3 ledger | Vector state with separated geometric and boundary channels |
| Final Green/Wronskian readout | Complex scalar obtained only after channel retention |
| `dslope` kernel | Total scalar two-point kernel, including the removable diagonal |
| Hilbert Gram kernel | Positive inner-product realization of that scalar kernel |
| Jacobi/height operator | Operator constructed from the certified moment pair |

Consequently:

$$
\boxed{\text{scalar equality}\ne\text{positivity proof}}
$$

and

$$
\boxed{\text{self-adjointness}\ne
\text{an unproved identification of every scalar zero with point spectrum}}.
$$

Every theorem that crosses one of these boundaries names the corresponding
certificate or representation explicitly.

## Completed Native HP Implication

[`CompletedNativeHPGateAudit.lean`](CarrySelfAdjointOperator/CompletedNativeHPGateAudit.lean)
formalizes the carrier-correct Hilbert--Polya implication and audits the older
complex-Taylor interface. The normalized product ledger contains the radial
phase and is not complex differentiable at the center. Consequently its first
odd complex Taylor jet is zero, and
`CompletedNativeGreenWeylReducedHeightCertificate` is uninhabited for that
state. The viable route uses real all-order jets on the completed TFVD/Hilbert
carrier.

```mermaid
flowchart LR
  T["real all-order TFVD/Hilbert carrier"] --> G["exact native moment Gram"]
  G --> J["positive closed Jacobi B*B"]
  J --> H["maximal self-adjoint signed height"]
  J --> R["global resolvent outside [0, infinity)"]
  R --> U["local analytic charts and resolvent uniqueness"]
  L["native Weyl germ at z = 0"] --> U
  U --> O["division-free ODE: 2 z m F + F' = 0"]
  O --> C["meromorphic order excludes Im(z) != 0"]
```

The carrier construction uses two interfaces that remain explicit and are not
conflated:

| Named interface | Exact content |
|---|---|
| `CanonicalCompletedNativeRealTfvdGreenMomentTransport` | One real jet in the concrete completed TFVD/Green Hilbert carrier, its injective all-order incidence transport, and its exact canonical native moment Gram; no isometry of the raw incidence Gram is assumed |
| `HasCanonicalCompletedNativeTfvdGreenCenterLegReadout` | The canonical polarized coefficient equals the complex Hilbert inner product of the same TFVD jets on every center--leg pair |

The division-free coefficient recurrence is no longer an input:
`polarizedGreenMomentCoefficient_coefficientEquation` proves it for the
canonical coefficient array. The constructor
`canonicalCompletedNativeRealTfvdGreenMomentTransport_of_centerLegReadout`
then derives all four parity blocks of the real moment Gram from the single
center--leg state readout, and
`completedNativeRealHPCarrierCertificate_of_centerLegReadout` adds both
all-order independence fields through the incidence transport.

`CompletedGreenForwardDifferenceVectorLimit` now performs the Hilbert-valued
completion without differentiating the state. It keeps two canonical steps
independent, proves the exact cross-kernel identity, obtains Cauchy convergence,
and constructs a limit jet with the canonical native moment Gram. The direct
constructor
`canonicalCompletedNativeRealTfvdGreenMomentTransport_of_vectorLimit_eq_projective`
feeds that jet into the HP carrier precisely when it is identified with the
already-built projective bracket-incidence jet. The scalar input is isolated as
`HasCompletedNativeGreenKernelTwoStepLimit`; it contains no vector or incidence
hypothesis.

[`CompletedNativePositiveJacobiResolvent.lean`](CarrySelfAdjointOperator/CompletedNativePositiveJacobiResolvent.lean)
constructs the unique global resolvent of the positive closed Jacobi operator
outside `[0, infinity)`. The analytic continuation is therefore no longer an
external pointwise hypothesis.

[`CompletedNativePositiveJacobiResolventAnalytic.lean`](CarrySelfAdjointOperator/CompletedNativePositiveJacobiResolventAnalytic.lean)
constructs bounded local analytic resolvent charts and identifies their cyclic
readout with the native Weyl germ near the Taylor center by uniqueness. The
identity principle then propagates the division-free equation

$$
2 z\,m(z)F(z)+F'(z)=0
$$

through the connected upper and lower cones. At an off-axis native zero, the
known order `-1` of `-F'/F` contradicts the nonnegative meromorphic order of
the analytic resolvent readout `2 z m(z)`. The resulting theorem is:

```lean
theorem completedNativeOperator_zero_im_eq_zero_of_positiveJacobiResolvent
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z : ℂ}
    (hzDomain : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    z.im = 0
```

Thus `HasGlobalGraphResolventAt` is not an input to the final theorem. The real
HP carrier certificate remains explicit and is supplied by the concrete TFVD/
Green moment-transport constructors described above.

### Direct signed-generator resolvent

The completed construction also globalizes the native Weyl germ without
passing through the resolvent of the positive square. In
[`CompletedNativeSignedGeneratorResolvent.lean`](CarrySelfAdjointOperator/CompletedNativeSignedGeneratorResolvent.lean),
the maximal self-adjoint signed generator is used directly:

$$
K=\begin{pmatrix}0&B^*\\B&0\end{pmatrix},
\qquad
(e_n,0)\mapsto(0,o_n)\mapsto(e_{n+1},0).
$$

Its cyclic-head coefficients are exactly the interleaved native moments,
with zero odd coefficients. Therefore the local graph equation

$$
x-zKx=e_0
$$

has scalar readout equal to the canonical native Weyl germ. Self-adjointness
alone makes `K-lambda` bijective for every nonreal `lambda`; no positivity
bound is used in that resolvent theorem. Bounded local charts, vector
uniqueness, and the same division-free ODE then give the direct conclusion:

```lean
theorem completedNativeOperator_zero_im_eq_zero_of_signedGeneratorResolvent
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z : ℂ}
    (hzDomain : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    z.im = 0
```

This route does not call the positive-Jacobi resolvent or assume
`HasGlobalGraphResolventAt`. It does not assert, without a separate theorem,
that every zero is already a point eigenvalue of the reciprocal height
operator. What it proves is the carrier-correct confinement implication from
the directly globalized signed-generator readout.

## Repository Map

| Layer | Main modules |
|---|---|
| Native geometry and recurrence | `NativeCausalBracket`, `NativeAllBasesCameraAtlas`, `NativeCameraResidueReflection` |
| Completed characteristic | `CompletedNativeCharacteristic`, `CompletedOperatorCharacteristic`, `CompletedProductJet` |
| Real moments | `CompletedNativeRealWeylMoments`, `CompletedNativeTfvdWronskianMoments` |
| Finite Jacobi and heights | `CanonicalLDLWhitening`, `CanonicalFiniteHeight`, `SignedFiniteHeightOperator` |
| Completed Green carrier | `CompletedNativeC3LedgerState`, `CompletedC3AllCutoffHilbertState`, `CompletedC3EnrichedSymplecticNoLeakBridge` |
| Completed native HP implication | `CompletedNativeHPConfinement`, `CompletedNativeHPGateAudit` |
| Scalar kernel bridge | `CompletedGreenRealKernelClosure`, `CompletedGreenForwardDifferenceLimit`, `CompletedC3FinalReadoutKernelBridge` |
| Vector Green completion | `CompletedGreenForwardDifferenceVectorLimit` |
| Gram positivity | `CompletedGreenForwardDifferenceGramBridge`, `BR2IncidenceStrictPositivity`, `GreenKernelCoefficientClosure` |
| Infinite operator | `GreenJetEnergyFactor`, `GreenJetMaximalAdjointSquare`, `GreenJetReciprocalSignedHeightOperator` |
| Weyl/resolvent readout | `CompletedNativeJacobiCyclicReadout`, `CompletedNativeJacobiWeylContinuation`, `CompletedNativeComplexGraphResolvent` |

## Supporting Notes

- [Causal bracket reconstruction and uniqueness](docs/causal-bracket-state-uniqueness.md)
- [Center/leg residue reflection](docs/bracket-residue-reflection-orbit.md)
- [Finite Green-jet/signed-height intertwiner](docs/canonical-green-jet-signed-height-intertwiner.md)
- [Completed Green-jet Hilbert space](docs/green-jet-signed-height-hilbert-space.md)
- [Global parity reflection](docs/green-jet-parity-reflection.md)
- [Energy-factor closability](docs/green-jet-energy-factor-closability.md)
- [Global reciprocal signed-height operator](docs/global-reciprocal-signed-height-operator.md)
- [Completed C3 Green/Wronskian frontier](docs/completed-c3-green-wronskian-frontier.md)

## Verification

```bash
lake build
bash scripts/audit.sh
```

The audit rejects `sorry`, checks the theorem surface, and reports the axioms
used by the exported results. GitHub Actions builds the exact dependency
checkout recorded by the repository.
