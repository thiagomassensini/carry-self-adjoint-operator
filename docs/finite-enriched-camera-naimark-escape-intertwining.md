# Finite enriched camera / completed Naimark escape

This branch starts at \`c22fffc631fd2d988465f3faf0d936aa02a7bb07\`.
It records the exact interface needed to compare the finite enriched camera
decomposition with the completed Naimark port/escape decomposition.

## Type and index audit

| object | domain/codomain | outer index | state/depth index | cutoff | metric/range |
|---|---|---|---|---|---|
| \`finiteCanonicalCameraReadout C\` | \`FiniteHilbertFamily state H ->_L[complex] FiniteHilbertFamily camera H\` | finite matrix row \`camera\` | finite matrix column \`state\` | implicit in \`C\` | standard finite \`PiLp\` family |
| \`finiteCanonicalCameraSynthesis C\` | \`FiniteHilbertFamily camera H ->_L[complex] FiniteHilbertFamily state H\` | finite matrix row \`camera\` | finite matrix column \`state\` | implicit in \`C\` | \`V = C^T G^(-1/2)\` |
| \`finiteCanonicalCameraProjection C\` | \`Matrix state state real\` | none after multiplication | state side | implicit in \`C\` | \`V R\`, finite state-side projection |
| \`finiteCanonicalCameraBlindProjection C\` | \`Matrix state state real\` | none after multiplication | state side | implicit in \`C\` | \`I - V R\`, complementary finite projection |
| \`finiteCameraInclusion bound\` | finite \`CameraFinsupp\` to \`CameraHilbert\` | \`CameraIndex\` label | none | camera-label bound | intrinsic Gram completion; isometric |
| \`cameraEmbedding\` | \`CameraFinsupp ->_li[real] CameraHilbert\` | \`CameraIndex\` label | none | none | completion of the raw Gram core |
| \`naimarkIsometry\` | \`CameraHilbert ->_li[real] NaimarkSpace\` | \`CameraIndex\` label | none | none | isometric Naimark extension |
| \`realifiedNaimarkPort\` | \`RealifiedCameraComplexification ->L[real] RealifiedNaimarkComplexification\` | camera completion | realified quadrature | none | bounded port \`U\` |
| \`realifiedNaimarkAdjoint\` | \`RealifiedNaimarkComplexification ->L[real] RealifiedCameraComplexification\` | camera completion | realified quadrature | none | canonical compression \`U^*\` |
| \`canonicalCompletedC3AmbientPortProjection\` | ambient realified Naimark to itself | none | ambient quadrature | none | \`U U^*\`, star projection |
| \`canonicalCompletedC3AmbientPortEscape\` | ambient realified Naimark to itself | none | ambient quadrature | none | \`I - U U^*\`, orthogonal escape |
| \`finiteEnrichedMovingCameraTfvdState C X\` | finite camera-family plus finite state-family, both \`CarryVerticalL2\`-valued | finite camera row | TFVD family coordinate | independent camera/TFVD cutoffs | visible readout plus finite blind complement |
| \`canonicalCompletedC3NaimarkState z\` | \`RealifiedNaimarkComplexification\` | completed camera realization | realified quadrature | completed C3 | existing completed ambient state |

The finite projection is on the matrix **state** side. The completed
projection is on the ambient Naimark side. The natural
\`finiteCameraInclusion\` has domain a finite subspace of intrinsic
\`CameraFinsupp\`, not the finite matrix state space. These are distinct
indices even when Lean assigns both an underlying natural-number type.

There are three different completion stories in the imported development:
the \`CameraHilbert\` completion of the Gram core, the projective TFVD/Gpre
completion, and the completed C3/TFVD/Green/Naimark carrier. This module
does not identify them.

## Exact factorisations

The new kernel-checked declarations are:

- \`finiteCanonicalCameraProjection_factorization\`:
  \`P_C = finiteCanonicalCameraSynthesis C * finiteCanonicalCameraReadout C\`.
- \`finiteCanonicalCameraBlindProjection_factorization\`:
  \`B_C = I - P_C\`.
- \`finiteCanonicalCameraProjection_hilbert_action\`: the same \`V R\`
  factorisation after lifting the matrix to any finite Hilbert-valued family.
- \`canonicalCompletedC3AmbientPortProjection_factorization\`:
  \`P_infty = realifiedNaimarkPort oL realifiedNaimarkAdjoint\`.
- \`canonicalCompletedC3AmbientPortEscape_factorization\`:
  \`B_infty = I - P_infty\`.

The finite projection idempotence facts require the finite row Gram
hypotheses already present upstream. The completed projection is already a
star projection by
\`canonicalCompletedC3AmbientPortProjection_isStarProjection\`.
The completed port/escape block is lossless by
\`canonicalCompletedC3NaimarkPortEscapeSynthesis_comp_readout\` and its
Pythagoras theorem.

## The exact remaining seam

For maps with the typed shape

\[
R : S \to A,\quad V : A \to S,\qquad
U : A_\infty \to N,\quad U^* : N \to A_\infty,
\]

a state embedding \(E : S \to N\), and a camera-coordinate transport
\(J : A \to A_\infty\), the missing squares are

\[
J R = U^* E,\qquad E V = U J.
\]

They are packaged by \`NaimarkProjectorIntertwiningSeam\`. The new theorems

- \`naimarkProjector_intertwines_of_squares\`,
  \`naimarkProjector_intertwines_of_seam\`;
- \`naimarkEscape_intertwines_of_squares\`,
  \`naimarkEscape_intertwines_of_seam\`;

prove, with no analytic assumptions, that these two squares imply

\[
E(VR)=(UU^*)E,\qquad
E(I-VR)=(I-UU^*)E.
\]

Pointwise forms are provided by
\`naimarkProjector_intertwines_apply_of_seam\` and
\`naimarkEscape_intertwines_apply_of_seam\`.

No concrete instance of the seam is constructed in this branch. The current
API has no theorem supplying an \(E\) from a finite matrix state family to
\`RealifiedNaimarkComplexification\`, nor a \(J\) identifying finite
whitened matrix coordinates with intrinsic \`CameraHilbert\` coordinates.
In particular, \`finiteCameraInclusion\` preserves the intrinsic Gram form,
while the finite matrix uses \`finiteCameraRowGram C = C C^T\`; no crosswalk
equates those forms for the generic finite state space. The finite square is
also complex-linear on \`FiniteHilbertFamily\`, while the completed port is a
realified continuous linear map. Thus the exact projector/escape statement
is reduced to the two missing typed squares rather than asserted by a cast.

This is also why no cutoff-dependent \(W_{M\to N}\) is claimed: finite
whitening \(G_M^{-1/2}\) changes with the camera cutoff, and the existing
inclusion theorems control only the unwhitened intrinsic Gram completion.
No theorem currently provides even an asymptotic projector intertwiner for
the moving whitened state.

## Reused completed results

The previous crosswalk proves the vector-valued completed roundtrip
\`canonicalCompletedC3NaimarkState_camera_roundtrip\`. The coisometric block
supplies the ambient decomposition and the nonzero witness
\`canonicalCompletedC3CoisometricNaimarkLeakLimit_ne_zero_at_witness\`.
The properness result
\`canonicalCompletedC3AmbientPortProjection_ne_one\` remains intact.
The new conditional theorems do not identify the escape with Gpre
provenance, and they do not alter the raw BR2 order-zero no-go.

## Status

- finite projector and blind factorisations: **closed**;
- completed projector and escape factorisations: **closed**;
- generic reduction from the two squares to projector/escape intertwining:
  **closed**;
- canonical finite \(E_M\) and whitened \(J_M\): **not supplied by the pin**;
- exact projector or blind intertwining for the concrete moving state:
  **not proved**;
- asymptotic moving-state intertwining: **not proved**;
- finite enriched pair embedded into a fixed port/escape carrier:
  **not proved**;
- completed visible and escape limits for the existing C3 induced source:
  **available** through
  \`canonicalCompletedC3FinitePortEscapeSource_tendsto\`;
- relation of Naimark escape to Gpre: **not identified**.

No new Hilbert completion, Naimark space, metric, normalization, or
orthogonality assertion was introduced.

## Next Metric/HP Gate

1. A finite embedding \(E_M\) is not available; only
   \`finiteCameraInclusion\` into \`CameraHilbert\` exists.
2. A whitened \(J_M\) is not available. The generic type
   \(A_M\to A_\infty\) remains the exact seam.
3. The visible readout square is not instantiated.
4. The synthesis square is not instantiated.
5. Projector intertwining is proved conditionally by
   \`naimarkProjector_intertwines_of_seam\`.
6. Blind/escape intertwining is proved conditionally by
   \`naimarkEscape_intertwines_of_seam\`.
7. No concrete exact or asymptotic equality is established.
8. The existing completed C3 induced source converges in the port-plus-escape
   carrier; the finite enriched moving family is not shown to be that source.
9. The completed blind object for that source is
   \`canonicalCompletedC3CoisometricNaimarkLeakLimit\`.
10. The corresponding visible object is
    \`canonicalCompletedC3CoisometricCompressedSourceLimit\`.
11. The escape is nonzero at the established witness.
12. No theorem identifies it with Gpre.
13. The raw BR2 order-zero no-go is unchanged.
14. There is no new lossless carrier for all moving finite jets.
15. The unique next theorem is a semantic finite-state-to-Naimark embedding
    together with the two squares above, or a proof that no canonical one
    exists for the chosen finite matrix family.
16. Only after that embedding/readout metric is identified can a comparison
    with the moment Gram be stated honestly; the HP/Hankel gate remains
    downstream.

## Validation

The audit file prints axioms for all new declarations and for the completed
projection/escape facts. Full build and audit results for this branch are
recorded in the final report.