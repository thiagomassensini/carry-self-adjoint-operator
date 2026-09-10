# Six-camera Cauchy/Weyl return variance crosswalk

## Scope and branch

This round starts at commit 231f467e58042a1995f253d3066ff7322dd78451 on
branch agent/six-camera-variance-weyl-return-crosswalk. The branch is
deliberately separate from main.

The implemented part is the typed compression of the existing all-bases
Cauchy block to the whitened six-camera coordinates, together with an exact
scalar third-order resolvent identity. No new completion, moment definition,
Weyl inverse, spectral list, TFVD, Genuine hypothesis, or Jacobi construction
was added.

The requested Weyl-return theorem is not claimed: the current pin has no
theorem connecting the global resolvent compression to the finite moment
matrices, and its Weyl inverse is a partial map. The missing connection is
recorded below instead of being filled by an unproved normalization.

## API and type audit

| object | exact type / carrier | convention |
|---|---|---|
| CameraHilbert | UniformSpace.Completion CameraFinsupp | real Hilbert space with the all-camera Gram completion |
| NaimarkSpace | Lp KolmogorovSpace 2 positiveLebesgueMeasure | real L2 realization |
| RealifiedCameraComplexification | WithLp 2 (CameraHilbert × CameraHilbert) | realification of a complexified camera space |
| allBasesCauchyBlock | RealifiedCameraComplexification →L[ℝ] RealifiedCameraComplexification | real block of the real and imaginary Cauchy components |
| allBasesCauchyRealPart | CameraHilbert →L[ℝ] CameraHilbert | naimarkAdjoint ∘ logarithmicResolventRealOperator ∘ naimarkIsometry |
| allBasesCauchyImaginaryPart | CameraHilbert →L[ℝ] CameraHilbert | same construction with the imaginary multiplier |
| allBasesCauchyPMap | full-domain LinearPMap on RealifiedCameraComplexification | bounded Cauchy block viewed through a subtype domain |
| allBasesWeylInverse | RealifiedCameraComplexification →ₗ.[ℝ] RealifiedCameraComplexification | LinearPMap.inverse; its domain is range allBasesCauchyBlock |
| sixCameraGram | Matrix (Fin 6) (Fin 6) ℝ | exact six-camera Gram |
| sixCameraFirstMoment | Matrix (Fin 6) (Fin 6) ℝ | existing finite first logarithmic moment |
| sixCameraSecondCenteredMoment | Matrix (Fin 6) (Fin 6) ℝ | existing finite second centered moment |
| sixCameraVariance | Matrix (Fin 6) (Fin 6) ℝ | existing whitened Schur-complement variance |
| sixCameraCauchyWhitenedHilbertSynthesisContinuous | EuclideanSpace ℝ (Fin 6) →L[ℝ] CameraHilbert | finite coordinates whitened with positiveInverseSqrt sixCameraGram |
| sixCameraCauchyRealifiedEmbedding | EuclideanSpace ℝ (Fin 6) →L[ℝ] RealifiedCameraComplexification | first component is the whitened embedding, second component is zero |
| sixCameraRealifiedCauchyCompression | EuclideanSpace ℝ (Fin 6) →L[ℝ] EuclideanSpace ℝ (Fin 6) | adjoint-compressed allBasesCauchyBlock |
| sixCameraCauchyRealPartCompression | EuclideanSpace ℝ (Fin 6) →L[ℝ] EuclideanSpace ℝ (Fin 6) | adjoint-compressed real component |
| sixCameraCauchyImaginaryPartCompression | EuclideanSpace ℝ (Fin 6) →L[ℝ] EuclideanSpace ℝ (Fin 6) | adjoint-compressed imaginary component |

The Fin 6 coordinate is an external camera-label coordinate. It is not a
coordinate of CameraHilbert, NaimarkSpace, or the inner state of the
realified block.

## Closed results

The module CarrySelfAdjointOperator/SixCameraCauchyMomentCrosswalk.lean
proves the following.

* sixCameraCauchyCameraFinsuppMap extends the six labelled coordinates by
  zero into CameraFinsupp.
* sixCameraCauchyCameraHilbertSynthesisLinear is the existing raw
  six-camera embedding, and its application is exactly
  atlasSixCameraHilbertEmbedding.
* sixCameraCauchyWhitenedHilbertSynthesisLinear and its continuous
  Euclidean version use the existing inverse square root of sixCameraGram.
* sixCameraCauchyWhitenedHilbertSynthesisContinuous_inner proves the exact
  Euclidean inner-product identity for that whitened embedding.
* naimarkIsometry_sixCameraCauchyWhitenedHilbertSynthesis identifies its
  Naimark realization with the already existing
  sixCameraWhitenedNaimarkSynthesis.
* sixCameraCauchyRealifiedEmbedding_toPair gives the exact realified pair
  (whitened embedding, 0).
* sixCameraRealifiedCauchyCompression_inner proves that the finite map is
  literally the adjoint compression of allBasesCauchyBlock.
* The real and imaginary component pairings are exposed by
  sixCameraCauchyRealPartCompression_inner and
  sixCameraCauchyImaginaryPartCompression_inner, using the existing
  logarithmic resolvent operators.
* scalar_resolvent_third_order and
  scalar_resolvent_third_order_of_offReal prove an exact scalar remainder
  identity. The specialized theorem
  scalar_logarithmicCoordinate_resolvent_third_order_of_offReal applies it
  to the existing coordinate logarithmicCoordinate x = 1 + log x.

The scalar identity is
\[
(\lambda-y)^{-1}
=
\lambda^{-1}+\lambda^{-2}y+
\lambda^{-2}y^2(\lambda-y)^{-1},
\]
with all factors kept explicit. It is an algebraic identity, not an
asymptotic statement.

## What is not proved

The source and its imports do not provide a bridge of the following form:

\[
\langle u,M_6(\lambda)v\rangle
=
\lambda^{-1}\langle u,v\rangle
+\lambda^{-2}\langle u,L_6v\rangle
+\lambda^{-3}\langle u,M_2v\rangle
+\text{controlled remainder},
\]

where M_6 is the above global Cauchy compression, L_6 is the whitened
first-moment operator, and M_2 is the whitened second moment.

In particular:

1. Finite/Moments.lean and Finite/Whitening.lean define and prove the
   finite moment/variance algebra, but do not identify those matrices with
   coefficients of allBasesCauchyBlock.
2. The resolvent multiplier is bounded off the real axis, while the proposed
   coefficient extraction requires an unbounded Y moment calculation.
   The current pin has no finite six-camera theorem that justifies the needed
   domain and integration interchange.
3. allBasesWeylInverse is a LinearPMap on range allBasesCauchyBlock, so an
   inverse expansion cannot be silently treated as an everywhere-defined
   six-by-six matrix.
4. No theorem in the inspected current graph proves that the inverse of a
   finite compression equals the compression of the global inverse. These are
   distinct objects:
   \[
   (PMP)^{-1}
   \quad\text{and}\quad
   PM^{-1}P.
   \]

Thus the following requested statuses remain open in this round:

* moment zero, one, and two as Cauchy coefficients;
* an admissible lambda path and a scaled Tendsto;
* invertibility of the compressed Cauchy family;
* a six-camera Weyl inverse defined from that compression;
* the sign and value of a first Weyl return coefficient;
* transport of the return coefficient to the previously proved halo plus global
  Naimark escape decomposition.

No Big-O, cutoff limit, camera cutoff, Genuine/zero hypothesis, TFVD object,
native-height object, Jacobi object, or camera-8 witness is used by the new
module.

## Why the current compression is the correct stopping point

The compression is not a separately invented finite matrix. It is defined by

\[
\text{finite whitened coordinates}
\longrightarrow
\text{realified CameraHilbert}
\overset{\texttt{allBasesCauchyBlock}}{\longrightarrow}
\text{realified CameraHilbert}
\longrightarrow
\text{finite adjoint}.
\]

The realified block has first and second components
\[
(Ax-By,\;Bx+Ay),
\]
where A and B are the existing real and imaginary logarithmic
resolvent compressions. The finite pairing theorems retain this orientation and
therefore do not make an unproved complex-linearity claim.

## Audit

SixCameraCauchyMomentCrosswalkAudit.lean prints the axioms for all principal
declarations, including the exact scalar remainder and all compression
pairings. The only axioms reported are the project axioms:

* propext;
* Classical.choice;
* Quot.sound.

There are no sorry, admit, or newly declared axioms.

The module is imported by:

* CarrySelfAdjointOperator.lean;
* CarrySelfAdjointOperator/Audit.lean;
* CarrySelfAdjointOperator/KernelConstructionAudit.lean.

A separate Weyl file was not added: all Cauchy-compression content that is
currently kernel-provable is consolidated in the Cauchy crosswalk, while a
separate Weyl-return theorem would require the missing moment/inversion bridge.

## Required next theorem

The smallest useful next theorem is a finite-dimensional matrix-element
asymptotic for the exact compression above. It must:

1. specify an admissible curve in the off-real lambda domain;
2. identify the first three matrix-element coefficients with the existing
   identity, whitened first moment, and whitened second moment;
3. prove a remainder limit without treating allBasesWeylInverse as total.

Only after that theorem should one use a finite-dimensional inverse expansion.
That expansion must state whether it defines inverse(compression) or a
compression of the global partial inverse. Once the choice is made and proved,
the first-return sign follows from the chosen resolvent convention. The
variance identity can then be supplied by the existing sixCameraVariance
Schur-complement theorem.

This next step is finite-dimensional and does not require TFVD or Gpre in
principle, but it is not available from the current pinned API.

## Required report answers

1. allBasesCauchyBlock is the real continuous-linear block on
   WithLp 2 (CameraHilbert × CameraHilbert).
2. allBasesWeylInverse is a real LinearPMap with domain the range of that
   block.
3. The six-camera Cauchy is a literal adjoint compression of the global block.
4. Moment zero has not been identified as a Cauchy coefficient.
5. Moment one is not yet identified; the target is the existing whitened
   first-moment matrix (sixCameraLogOperator / whitenedFirstMoment).
6. Moment two is not yet identified; the target is
   sixCameraWhitenedSecondMoment.
7. An exact scalar third-order remainder identity is proved, but not its
   compressed/integrated form.
8. No Big-O is used.
9. No lambda parametrization is used; only the hypothesis lambda.im != 0.
10. Invertibility of a six-camera compressed Cauchy is not proved.
11. No six-camera Weyl inverse is defined.
12. Yes: inverse(compression) and compression(inverse) remain explicitly
    distinct.
13. No first-return sign is claimed.
14. No equality with sixCameraVariance is claimed.
15. The available remainder is an exact scalar expansion, not a Tendsto.
16. The previously proved halo plus global escape identity was not transported
    to a Weyl coefficient.
17. No camera-8 result is used.
18. No cutoff or camera limit is used.
19. No Genuine/zero hypothesis is used.
20. No native-height or Jacobi object is used.
21. The next theorem is the finite compressed matrix-element asymptotic followed
    by a finite inverse expansion.
22. This next step can be attempted without TFVD/Gpre, but it still needs the
    unproved resolvent-to-moment bridge and the inverse/compression choice.
