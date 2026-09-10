# Atlas Energy six-camera Hilbert asymptotic crosswalk

Base: 389f88105c614813afb2baabc825fd23ecfe653a
Branch: agent/atlas-energy-camera-hilbert-asymptotic-embedding

This round uses the historical repository genuine-zero-uniform-atlas-energy as
an archaeological source.  Its snapshot
a174bc3b3a53a9d32d0c66d4c037477263f1a8c7
(v0.14.0, exact six-camera second-jet crosswalk) contains
EmpiricalCameraHigherDerivativeCrosswalk.lean.  The current project does not
add that repository as a dependency.  The current pinned
NativeCarrySpectralWeyl camera API is sufficient for the finite crosswalk and
for the limiting Gram calculation.

The historical file proves the following equalities in its own namespace:
spectralCameraRadiusSet_eq_empiricalRadii,
spectralCameraAlignedCenter_eq_empiricalCenter,
realDirichletPower_natCast_eq_spectralDirichletValue,
realCpPairBracket_eq_spectralCenteredBracketTerm,
empiricalCameraSeed_eq_spectralCameraSeed,
empiricalCameraBlock_eq_spectralCameraBlock,
empiricalCameraCharacteristic_eq_spectralCameraCharacteristic,
finiteEmpiricalCameraCharacteristic_eq_spectralCameraCharacteristic, and
criticalLineParameter_eq_spectralCameraNativeLine.  It also transports the
all-order derivative tail.  This module reproduces the smallest current-side
version of that geometry without importing the historical project.

## Three distinct Gram/completion layers

| object | domain and codomain | cutoff | metric |
|---|---|---:|---|
| finite row Gram | Fin 6 by Fin 6 real matrix, finiteLiteralSixCameraMatrix | camera coefficient cutoff | raw C C^T |
| normalized finite Gram | Fin 6 by Fin 6 real matrix | same camera cutoff | A_M = M^-1 G_M |
| CameraHilbert embedding | Fin 6 real coefficient functions to CameraHilbert | no finite cutoff | limiting sixCameraGram / intrinsic gramForm |

The finite prefix or state cutoff is a separate parameter from the camera
coefficient cutoff.  No state coordinate is identified with a camera label.

The all-bases camera completion is the existing
NativeCarrySpectralWeyl.Infinite.CameraCompletion construction:
CameraFinsupp is supported camera coefficients, CameraHilbert is its intrinsic
Gram completion, cameraVector is the completed vector of one camera, and
cameraEmbedding is the canonical isometry.  The TFVD and C3/Green completions
remain separate carriers.

## Historical six-camera semantics

The current finite package uses labels sixCamera i = i + 2.  The module
defines atlasSixCameraIndex as the corresponding supported CameraIndex and
proves atlasSixCameraIndex_injective.

The historical period list is
4, 3, 4, 5, 6, 7 and the historical radius list is
{1}, {1}, {1,2}, {1,2}, {1,2,3}, {1,2,3}.  The kernel-checked current
crosswalks are:

- atlasSixCameraHistoricalPeriod_eq_cameraSlope;
- atlasSixCamera_radiusSet_eq_historical;
- atlasSixCamera_alignedCenter_eq_historical;
- atlasSixCamera_supported.

Thus the labels, slopes, radius sets, and aligned centers agree at finite
level with the Spectral-Weyl definitions.  The existing
finiteBracketCharacteristic_tendsto and
iteratedDeriv_bracketCharacteristic_nativeLine_tail_le are specialized by
atlasSixCamera_finiteCharacteristic_tendsto and
atlasSixCamera_iteratedDeriv_tail_le.  No new characteristic or empirical
camera definition is introduced.

## Raw finite and limiting Gram

The definitions
atlasRawFiniteSixCameraRowGram and
atlasNormalizedFiniteSixCameraRowGram keep raw and normalized finite metrics
separate.  The theorem
atlasRawFiniteSixCameraRowGram_apply identifies raw entries with
literalFiniteCameraGram, while
atlasNormalizedFiniteSixCameraRowGram_tendsto is exactly the existing
normalized finite six-camera convergence to sixCameraGram.

The current-side intrinsic embedding is

    atlasSixCameraHilbertEmbedding c
      = sum i, c i • cameraVector (atlasSixCameraIndex i).

The theorem
atlasSixCameraGram_entry_eq_gramKernel proves, entry by entry, that the exact
six-camera matrix is the all-bases Gram kernel restricted to labels 2 through
7.  Consequently:

    inner (atlasSixCameraHilbertEmbedding c)
      (atlasSixCameraHilbertEmbedding d)
      = c dotProduct (sixCameraGram *ᵥ d)

by atlasSixCameraHilbertEmbedding_inner.

For one-coordinate vectors this becomes the exact overlap formula
atlasSixCameraHilbertEmbedding_coordinate_inner.  Raw axes are not
orthogonal: atlasSixCamera_raw_overlap_2_4 proves that the overlap of labels 2
and 4 is 10.  This is a concrete witness that the algebraic camera package
and its direct-sum bookkeeping are not a raw orthogonal decomposition.

## Candidate finite whitening embedding

The investigated candidate is defined without a new completion:

    atlasSixCameraWhiteningMatrix M
      = positiveInverseSqrt (atlasNormalizedFiniteSixCameraRowGram M)

    atlasSixCameraWhitenedHilbertEmbedding M c
      = atlasSixCameraHilbertEmbedding
          (atlasSixCameraWhiteningMatrix M *ᵥ c).

This is the natural current-side version of
J_M c = I_6 (A_M^(-1/2) c), with I_6 the raw six-camera embedding into
CameraHilbert.  It is deliberately defined even before eventual positive
definiteness of every finite normalized Gram is proved; no false finite
isometry assertion is made.

The exact pairing is the theorem
atlasSixCameraWhitenedHilbertEmbedding_inner:

    inner (J_M c) (J_M d)
      =
    c dotProduct
      ((W_M^T sixCameraGram W_M) *ᵥ d),

where W_M is atlasSixCameraWhiteningMatrix M.  This derives the metric from
the raw embedding and does not postulate a tensor-product metric.

The conditional theorem
atlasSixCameraWhitenedHilbertEmbedding_inner_tendsto_of_inverseSqrt_tendsto
proves the desired asymptotic isometry from the single explicit hypothesis

    W_M -> positiveInverseSqrt sixCameraGram.

Its proof uses continuity of finite matrix multiplication and the existing
positiveInverseSqrt_whitens theorem.  The current pin has no theorem giving
continuity of positiveInverseSqrt as a matrix-valued function of a positive
definite matrix.  Therefore the inverse-square-root convergence is the exact
remaining analytic seam.  No convergence of the naked whitening matrices is
claimed.

## Naimark and blind status

This round does not add an embedding from a finite state/stencil carrier into
the completed C3 ambient Naimark space.  The existing
NaimarkProjectorIntertwiningSeam remains the typed interface for that
state-side problem.

The completed Naimark port, its adjoint, projection, and escape are already
defined elsewhere.  They are not identified here with finite
finiteCanonicalCameraProjection or finiteCanonicalCameraBlindProjection:
the domains and the cutoff-dependent whitening matrices are different.

Likewise, Atlas Energy rho is not identified with a finite camera blind norm.
rho is the transverse-to-clock energy in the historical empirical stack,
whereas the finite blind projection is the complement of the finite camera
readout range.  No theorem in the current pin maps either one to the
Naimark escape or to the Gpre provenance carrier.

## Kernel-checked results

The new module is
CarrySelfAdjointOperator/AtlasEnergySixCameraHilbertAsymptoticCrosswalk.lean.
Its audit companion is
CarrySelfAdjointOperator/AtlasEnergySixCameraHilbertAsymptoticCrosswalkAudit.lean.

The audited public results include:

- exact historical labels, periods, radii, centers, and support;
- finite characteristic convergence and all-order derivative tail transport;
- raw finite Gram entry formula;
- normalized finite Gram convergence;
- six-camera Gram entry equality with gramKernel;
- raw CameraHilbert pairing and single-coordinate pairing;
- nonzero raw 2/4 overlap;
- exact whitened pairing formula;
- conditional asymptotic-isometry reduction.

The audit output for these theorems contains only the accepted standard
axioms: propext, Classical.choice, and Quot.sound.  There is no sorryAx,
admit, or new axiom.

## Next Blind/HP Gate

1. The Atlas Energy six cameras are formally crosswalked to the current
   Spectral-Weyl labels, radii, centers, and finite characteristic formulas.
2. The crosswalk is finite and all-order on the derivative-tail side; the
   historical empirical theorem itself is not a dependency.
3. A_M is the explicitly defined cutoff-normalized raw row Gram.
4. A_M tends to sixCameraGram exactly by
   atlasNormalizedFiniteSixCameraRowGram_tendsto.
5. J_M is the whitened embedding above.
6. Its exact pairing is closed; finite exact isometry is not claimed.
7. Asymptotic isometry is conditional on inverse-square-root continuity/convergence.
8. The visible CameraHilbert raw embedding is closed at the six-camera level.
9. A concrete state-side E_M and the finite-to-Naimark readout square remain
   open.
10. The finite blind kernel is the state-side kernel of the finite readout;
    the completed escape kernel is the ambient Naimark complement.
11. No canonical map between these kernels is supplied by the current APIs.
12. Atlas rho represents a different projection (away from a clock tangent).
13. The raw BR2 order-zero no-go remains untouched.
14. The next minimum metric theorem is a finite-dimensional continuity result
    for positiveInverseSqrt (or an equivalent Cholesky/LDL perturbation result)
    applied to A_M -> sixCameraGram.
15. Only after that theorem can one assert asymptotic isometry of J_M.
16. The next HP theorem still needs a carrier-level crosswalk from these
    whitened camera modes to the all-order completed Green/TFVD state.  A
    moment Gram or Hankel identity is not licensed by this round.
