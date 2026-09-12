# Native source-locus Green compatibility

This branch audits the two boundary charts that are obtained from the same
canonical structured C3 state. The question is restricted to that source
locus; no map on the ambient C3 port space is introduced.

## Common ancestor

For a parameter z, the common state is

~~~lean
canonicalCompletedC3StructuredOnePointState z
  : CanonicalC3BracketTfvdCompletionState 1
~~~

The Gamma projection reads its greenPort, packs it with

~~~lean
canonicalC3SixCameraSourceMap
~~~

and applies the existing

~~~lean
carryGammaComplexCauchyReadout
~~~

The native scalar projection reads the normalized log-jet and value channels
in the order required by greenForm:

~~~lean
(canonicalC3BracketTfvdNormalizedLogJetReadout 1 z,
 canonicalC3BracketTfvdNormalizedValueReadout 1 z)
~~~

On the genuine strip the existing tail crosswalk identifies this pair with

~~~lean
canonicalNativeUndressedScalarBoundaryPair z
  = (nativeHeightScalarBoundaryCompanion z, nativeHeightScalar z)
~~~

and hence with (-deriv nativeHeightScalar z, nativeHeightScalar z).

## Exact source-locus channel

The module
~~~text
CarrySelfAdjointOperator/NativeSourceLocusGreenCompatibility.lean
~~~
defines

~~~lean
canonicalCompletedC3NativeSourceLocusGammaGreenForm z w hz hw
~~~

as the Green form of the structured Gamma projection and

~~~lean
canonicalCompletedC3NativeSourceLocusScalarGreenForm z w
~~~

as the Green form of the normalized undressed projection.

The sole explicitly retained channel is

~~~lean
canonicalCompletedC3NativeSourceLocusProjectionMismatch z w hz hw
  = GammaGreenForm z w - ScalarGreenForm z w.
~~~

No nativeXiCompletionFactor, characteristic dressing, moment sequence,
Hankel matrix, Jacobi operator, or HP object occurs in this definition.

On the genuine strip, the exact existing identity gives

~~~text
projectionMismatch
  =
canonicalCompletedC3PureNativeBoundaryMismatch.
~~~

Equivalently, in division-free form,

~~~text
projectionMismatch
  =
canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw
  - completedGreenWronskian
      nativeHeightScalar nativeHeightScalarBoundaryCompanion w z.
~~~

Thus the first divergent object is identified: it is the comparison of the
six-camera Gamma/Cauchy projection with the normalized value/log-jet
projection of the same structured state. No additional channel has been
silently removed.

## Source-locus relation

The pointwise relation is named

~~~lean
CanonicalCompletedC3NativeSourceLocusGreenCompatibilityAt z w hz hw
~~~

and the all-pairs canonical-family relation is

~~~lean
CanonicalCompletedC3NativeSourceLocusGreenCompatibility
~~~

The exact equivalence is

~~~text
CanonicalCompletedC3NativeSourceLocusGreenCompatibility
↔
∀ z w hz hw, projectionMismatch z w hz hw = 0.
~~~

On the genuine strip it is pairwise equivalent to the previously isolated
pure-native sewing equation. This is a reduction, not a proof that the
channel vanishes.

## Cancellation/Gpre audit

The existing cancellation carrier is reused through

~~~lean
canonicalCompletedC3NativeSourceLocusCancellation_greenDefect_eq_verticalWronskian
~~~

It retains the Green response, boundary return, and provenance coordinates.
The CPFormal glued-boundary theorem identifies its Green defect with the
carry-weighted vertical Wronskian. Provenance cancels inside that Green
defect, but no theorem in this branch identifies that vertical Wronskian with
the Gamma projection versus the native scalar projection. Therefore Gpre
does not discharge the source-locus channel.

## Status

| Gate | Status |
| --- | --- |
| Common structured ancestor | CLOSED EXISTING |
| Gamma projection expansion | CLOSED THIS BRANCH |
| Normalized undressed scalar expansion | CLOSED EXISTING |
| Scalar projection equals native undressed form on strip | CLOSED EXISTING |
| Pure mismatch equals the projection mismatch | CLOSED THIS BRANCH |
| Division-free Gamma-readout minus native Wronskian | CLOSED THIS BRANCH |
| Source-locus relation and zero-mismatch iff | CLOSED THIS BRANCH |
| Gpre cancellation/vertical-Wronskian crosswalk | CLOSED THIS BRANCH |
| Gamma Green form equals native scalar Green form | OPEN |
| Pure mismatch vanishes | OPEN |
| Ambient/global Green intertwiner | OBSTRUCTED in the previously proved bare-packing scope |

The prior bare-packing no-go concerns all of the ambient
FiniteC3GreenPortCarrier 3; it is not applied here as a source-locus no-go.
The diagonal real-part-zero and skew-Hermitian identities remain constraints
on the channel, not a vanishing theorem.

## Outcome

Outcome B: the remaining source-locus mismatch is isolated as one exact
structural channel, with no dressing or downstream HP material in its
definition. The next minimum theorem is a source-locus identity connecting
the Gamma/Cauchy readout of the packed greenPort to the Green form of the
normalized log-jet/value projection. A global linear intertwiner is neither
needed nor claimed.
