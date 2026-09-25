# Checkpoint — ordinary six-source roles require an affine boundary ledger

## What is now theorem

`CompletedNativeCameraResolvedOrdinaryAffineSeed.lean` makes the existing C3
prefix law explicit as a boundary-plus-gradient identity:

\[
\operatorname{positiveDirichletValue}(s,3m)
= \operatorname{canonicalOrdinaryBoundarySeed}(s)
  + \sum_{n<3m}\operatorname{positiveDirichletGradient}(s,n),
\qquad
\operatorname{canonicalOrdinaryBoundarySeed}(s)=1.
\]

The resulting `canonicalOrdinaryAffineSeededData m s` is proved literally
equal to `C3TraceDynamics.nativeBlockSeededData m s`; after `seededRecover`,
it reconstructs the same four native nodal values.  The result applies
uniformly to the `z`, `w`, and reflected-`z` parameter presentations.  The
seed is intentionally global boundary data, never assigned to a camera.

## What is now additionally theorem

`CompletedNativeCameraResolvedOrdinaryGradientPromotion.lean` supplies the
missing ordinary-gradient camera family, while preserving the unit atom as a
boundary datum.  It first resolves the boundary-free value by the existing
logarithmic factorization:

\[
V^{\partial}_{s}(n)=
\begin{cases}
0,&n=0,\\
\dfrac{D_s(n)-1}{\log(n+1)}\,v_{n+1},&n>0,
\end{cases}
\qquad
\operatorname{synth}(V^{\partial}_{s}(n))=D_s(n)-1,
\]

where \(D_s(n)=\operatorname{positiveDirichletValue}(s,n)\) and \(v_{n+1}\)
is the already canonical camera contribution vector.  Taking adjacent
differences gives a camera-resolved ordinary gradient

\[
G_s(n)=V^{\partial}_{s}(n+1)-V^{\partial}_{s}(n),
\qquad
\operatorname{synth}(G_s(n))=
\operatorname{positiveDirichletGradient}(s,n).
\]

This is not a redistribution of the atom \(1\): the ordinary value is kept in
the affine ledger as \(1,V^{\partial}_s\), and only its gradient is supplied
to the TFVD analysis.  In particular, the earlier residual for reusing the
logarithmic **value** resolver remains true and unchanged.

The exact synthesis is now compiled for all three ordinary parameter roles
\(z,w,z^\sharp\), and it is combined with the already compiled three log-jet
roles.  The outcome is a finite external-camera family indexed by `ℕ` whose
sum is literally `nativeC3SeededClockTfvdSixSourceAnalysis`.  The six source
roles remain typed independently of external camera labels; no boundary
context was identified with a prime or a camera.

## Exact next seam

The next step is deliberately separate: transport this finite sum through
`canonicalC3AllCutoffMixedSourceTfvdReconstruction` and the direct/reflected
Green-port extractors.  The remaining work is an additivity adapter for the
nested `WithLp` reconstruction carrier.  It is not an ordinary-role or
boundary-seed obstruction.

Until that adapter is formalized, `greenProvenance`, `offDiagonal`,
`readoutResidual`, `tailCompletion`, and `archimedeanChart` remain global
terms.  No claim is made here that either Green port is already a finite sum,
or that its pairwise and boundary-camera cross terms vanish.
