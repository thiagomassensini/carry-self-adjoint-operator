# Camera-resolved six-source promotion: log roles and ordinary boundary obstruction — 2026-09-25

## Decision

The repository now has a real camera-resolved promotion for exactly the three
`logJet` roles of the seeded completed six-source datum, at the three complex
parameters `z`, `w`, and `reflectedParameter z`.  It does **not** yet have a
promotion for the three ordinary roles.  The correct status is therefore
**BLOCKED before the direct/reflected Green ports**, with a concrete local
obstruction rather than a missing theorem disguised as a hypothesis.

This does not change the prior overall classification of the corrected
response as **MIXED**: should both ports later be resolved, the Green term is
pairwise, while provenance, residual, tail, and chart remain distinct global
coordinates.

## Compiled log-role promotion

`CompletedNativeCameraResolvedSixSourceLogJetPromotion.lean` extends the
existing finite-support factorization-camera construction from `nativeLine t`
to arbitrary `s : Complex`:

```lean
cameraResolvedLogSlopeChannelAt
finiteCameraResolvedLogSlopePrefixStateAt
cameraResolvedSeededClockLogJetTfvdAnalysis
cameraResolvedSeededClockLogJetParameterAnalyses
```

Its main equations are:

```lean
finiteCameraResolvedLogSlopePrefixStateAt_synthesis_eq_completedTfvd
cameraResolvedSeededClockLogJetTfvdAnalysis_synthesis_eq_seededClock
cameraResolvedSeededClockLogJetParameterAnalyses_synthesis_eq_role
```

For each `parameter : CanonicalC3SixSourceParameterRole`,

\[
\operatorname{lsum}\bigl(A^{\log}_{\mathrm{parameter},r}\bigr)
=
\texttt{canonicalC3SixSourceRoleAnalysis}
  (\texttt{nativeC3SeededClockTfvdSixSourceAnalysis}\ M\ q\ S\ z\ w)
  (\mathrm{parameter},\mathrm{logJet}).
\]

The outer index is honestly `camera : Nat`; it is neither a boundary context
nor a prime certificate.

## Exact ordinary-role residual

The presently available camera construction distributes the logarithmic
factorization ledger.  At its initial positive vertex it is zero:

\[
\operatorname{cameraResolvedLogDirichletValue}(s,0)=0,
\qquad
\operatorname{positiveDirichletValue}(s,0)=1.
\]

The compiled residual is:

```lean
cameraResolvedOrdinaryBoundaryReuseResidual s :=
  positiveDirichletValue s 0 -
    cameraComplexSynthesis (cameraResolvedLogDirichletValue s 0)
```

with

```lean
cameraResolvedOrdinaryBoundaryReuseResidual_eq_one
canonicalC3SixSourceOrdinaryRole_logCameraReuseResidual_eq_one
```

proving

\[
\boxed{\operatorname{Residual}_{\mathrm{ordinary}}(s)=1.}
\]

This is a no-go only against *reusing the current logarithmic camera resolver*
for `ordinary`.  It does not preclude a future boundary-aware ordinary camera
channel.  Such a channel must carry the initial/incoming boundary atom in
addition to the factorization-camera log ledger; no existing object supplies
that channel.

## Consequence for the Green-port target

No full camera-resolved six-source datum has been constructed.  Hence no
camera-resolved direct or reflected port exists yet, and the pairwise theorem
from `CompletedNativeCameraResolvedGreenPairwise.lean` has deliberately not
been applied to canonical source data.

The exact next seam is now narrower than before:

\[
\boxed{
\text{boundary-aware ordinary camera channel}
\longrightarrow
\text{three ordinary roles at }z,w,z^\sharp.
}
\]

Once that channel is present, it can be paired with the already compiled
three log-role families, analyzed/reconstructed channelwise, and only then
used to obtain direct/reflected port decompositions and the already compiled
pairwise Green formula.
