# Camera-resolved corrected six-source seam — 2026-09-25

## Result of the audit

The current formal resolution is **MIXED**.  This is a statement about the
available, provenance-preserving architecture; it is not a claim that a
diagonal camera formula has been disproved for some future stronger lift.

1. The logarithmic TFVD channel is resolved by a finitely supported camera
   label `p : Nat` and synthesizes exactly to the completed log-jet prefix.
2. The other five-source provenance is retained by the six-role TFVD datum
   and its reconstruction, but no compiled map resolves all six roles by the
   outer camera label.
3. The corrected boundary is a Green pairing of reconstructed direct and
   reflected ports, hence would be pairwise/matrix-valued under a full camera
   resolution.
4. The final corrected response additionally retains Green provenance,
   off-diagonal readout, local residual, tail completion, xi weight, and the
   archimedean chart.  These are not camera-diagonal terms and must remain as
   separately typed contributions.

## The compiled pieces

The existing channel theorem is

```lean
finiteCameraResolvedLogSlopePrefixState_synthesis_eq_completedTfvd
```

with outer type

```lean
CameraResolvedCarryVertical = Nat →₀ CarryVerticalL2.
```

The synthesis commutes with TFVD analysis and reconstruction through

```lean
cameraChannelAnalysisSynthesis_tfvdAnalysis_commutes
cameraChannelTfvdReconstruction_analysis_synthesis.
```

This is an exact channelwise statement, but it currently applies to the
log-jet prefix on the native real line.  It does not supply camera-resolved
ordinary, reflected, and three-parameter six-source data.

Separately, the actual corrected boundary already has a pre-scalar vector
realization:

```lean
canonicalC3SixSourceSymplecticNaimarkVector
canonicalC3SixSourceSymplecticNaimarkReadout_eq_correctedBoundary.
```

It retains direct, reflected, and quarter-turned reflected ports and reads
the complex Green value through two real skew quadratures.  The complete
ledger then adds its structural, tail, and chart coordinates before the final
scalar readout.

## Exact pairwise theorem

`CompletedNativeCameraResolvedGreenPairwise.lean` proves, for arbitrary
finite families of ports,

\[
\operatorname{greenForm}\!\left(
  \sum_{r\in A}P_r,\ \sum_{q\in B}Q_q
\right)
=
\sum_{r\in A}\sum_{q\in B}
  \operatorname{greenForm}(P_r,Q_q).
\]

The summation genuinely ranges independently over `r` and `q`.  Thus, if
both direct and reflected ports are later lifted camera-wise, every
off-diagonal contribution `r ≠ q` belongs to the exact formula.  No
diagonal-only reduction follows from linear synthesis.

The final scalar response is exactly

\[
\begin{aligned}
R={}&\xi\bigl(
  \operatorname{CorrectedBoundary}
  +\operatorname{Structural}(\operatorname{greenProvenance},
      \operatorname{offDiagonal},\operatorname{readoutResidual})
  +\operatorname{tailCompletion}
\bigr)\\
&+\operatorname{archimedeanChart}.
\end{aligned}
\]

This equality is currently a compiled definitional theorem, not a linearized
ansatz.

## Why the next arrow is still missing

There are two formal source carriers with no instantiated map between them:

```lean
CanonicalC3SixSourceToCameraChannelAnalysis S
```

is the desired provenance-aware promotion

```lean
CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S →ₗ[ℂ]
  (Nat →₀ NativeGpreFiniteTfvdAnalysisCarrier S),
```

while

```lean
CanonicalC3SymplecticNaimarkToFiniteCameraFamily
```

is the later real-linear promotion from the corrected symplectic Naimark
triple to the finite historical camera family.  The repository intentionally
defines both *types* but provides no inhabitant.  This is a genuine seam, not
a hypothesis used below it.

There is also no theorem that converts an arbitrary
`NativeGpreBoundaryContext` to `Nat.Primes`: its `arithmeticPrime` and
`towerPrime` fields are wrapper naturals explicitly documented as carrying no
primality certificate.  Hence neither the boundary-context finset nor the
camera-label support may be silently identified with a prime atlas.

## Consequence for the Riesz route

No family

\[
r\longmapsto g^{R}_{r,k},\quad r\longmapsto g^{I}_{r,k}
\]

has yet been produced from the corrected six-source response.  Consequently,
there is no legitimate input to `nativeGpreFiniteTowerRieszSynthesis` for a
corrected order `k`, and no defect-form first-column comparison has been
attempted.

The next correct construction is a full six-role, camera-resolved promotion
that proves a synthesis identity for the three ordinary/log-jet source pairs.
Only after that map exists can one decide whether the completed scalar
response has a pure vector decomposition, a pairwise kernel, or a mixed
linear-plus-pairwise form in the actual camera family.
