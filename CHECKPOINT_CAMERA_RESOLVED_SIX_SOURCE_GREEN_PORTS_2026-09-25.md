# Checkpoint — the completed six-source Green boundary is camera-pairwise

## Exact result

The affine ordinary seed is upstream of TFVD and cancels when passing to the
ordinary gradient.  Consequently the already proved finite camera synthesis
of the six TFVD analyses transports linearly through the complete
reconstruction and through both Green-port extractors:

\[
\sum_{r\in A}X_r=X_{\rm canonical},\qquad
\sum_{r\in A}P_r=P_{\rm canonical},\qquad
\sum_{r\in A}Q_r=Q_{\rm canonical}.
\]

Here \(A\) is the finite support of external labels `camera : ℕ`,
\(X_r\) is the reconstruction of camera \(r\)'s complete six-role analysis,
and \(P_r,Q_r\) are respectively its direct and reflected Green ports.
No `NativeGpreBoundaryContext` is identified with a camera or a prime.

The reconstruction itself is not previously packaged as one global linear
map.  Its definition is coordinatewise, using six instances of the existing
continuous-linear map `nativeGpreFiniteTfvdReconstruction`.  The new module
proves the minimal consequences: additivity and finite-sum preservation.

## Pairwise kernel

The individual resolved kernel is

\[
K_{r,q}(z,w)=\operatorname{greenForm}(P_r(z,w),Q_q(z,w)).
\]

The corrected boundary is now exactly

\[
\boxed{
\operatorname{CorrectedBoundary}(z,w)
=\sum_{r\in A}\sum_{q\in A}K_{r,q}(z,w).
}
\]

This is a functional, pre-jet identity.  It retains all diagonal and
off-camera terms literally.  No theorem in this checkpoint says that a term
with \(r\ne q\) vanishes or is nonzero; diagonalization has not been assumed.

## What remains global

The result resolves only the corrected Green boundary.  The completed final
readout continues to retain separately its global
`greenProvenance`, `offDiagonal`, `readoutResidual`, `tailCompletion`,
mixed Hermitian weight, and `archimedeanChart` terms.  None was treated as a
gauge coordinate or compressed into the Green double sum.

## Classification

The Green component is now `CAMERA-PAIRWISE GREEN`; the entire final readout
remains `MIXED`.  The next legitimate step is to transport this exact
functional pairwise identity through real/complex quadratures and then jets,
not to introduce Riesz, a defect form, a moment carrier, or a first-column
claim here.
