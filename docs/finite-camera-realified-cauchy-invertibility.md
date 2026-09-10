# Finite camera realified Cauchy invertibility

This crosswalk adds the finite complex Cauchy family in the explicit realification used by the pinned Spectral-Weyl API. It starts from a finite camera family camera : I -> CameraIndex, with Fintype I and DecidableEq I, and a supplied matrix G identified with the raw Naimark Gram and assumed G.PosDef when strictness or inversion is needed.

## Carriers and old six-camera object

The finite coordinate carrier is

```lean
FiniteCameraCoordinates I := EuclideanSpace Real I
```

and the complete finite complex realification is

```lean
FiniteCameraRealification I :=
  WithLp 2 (FiniteCameraCoordinates I x FiniteCameraCoordinates I).
```

The previous sixCameraRealifiedCauchyCompression has type
EuclideanSpace Real (Fin 6) ->L[Real] EuclideanSpace Real (Fin 6). Its embedding puts a real vector in the first coordinate of the global realification and therefore is a one-coordinate/component compression. This file introduces sixCameraRealifiedCauchyBlock, whose domain and codomain are the full FiniteCameraRealification (Fin 6).

The conversion from EuclideanSpace to the finite camera synthesis is explicit (ofLp/toLp); no coordinate of NaimarkSpace is identified with a camera label.

## Finite compression

finiteCameraWhitenedNaimarkSynthesisContinuous is the continuous linear lift of the existing whitened synthesis. The real and imaginary compressions are finiteCameraCauchyRealPart and finiteCameraCauchyImaginaryPart. They are defined by adjoint composition with the pinned bounded operators logarithmicResolventRealOperator and logarithmicResolventImaginaryOperator. Their pairing theorems transport the global resolvent pairings without redoing the multiplier calculation. The strict imaginary signs are inherited from the global Herglotz lemmas:

* 0 < lambda.im gives a strictly negative quadratic form;
* lambda.im < 0 gives a strictly positive quadratic form.

The full block is the literal real 2 x 2 block

```text
(x,y) |-> (A x - B y, B x + A y).
```

finiteCameraRealifiedCauchyBlock_inner_ambient records its equality with the pairing of the realified finite Naimark embedding and the pinned ambient logarithmicResolventBlock. This pairing form is the semantic compression theorem; no independent finite matrix formula is introduced.

## Invertibility and intrinsic Weyl

The block skew quadratic is the sum of the two imaginary quadratic forms. Hence it is strictly negative in the upper half-plane and strictly positive in the lower half-plane for every nonzero finite-realified vector. The block is therefore injective for lambda.im != 0; surjectivity is obtained only from finite-dimensional linear algebra (LinearMap.injective_iff_surjective). No determinant or numerical calculation is used.

The inverse is bundled as the opposite LinearEquiv of finiteCameraRealifiedCauchyEquiv, then exposed as the everywhere-defined continuous linear map finiteCameraIntrinsicWeylBlock. The two-sided laws are:

```lean
finiteCameraIntrinsicWeylBlock_comp_cauchy
finiteCameraRealifiedCauchyBlock_comp_intrinsicWeyl
```

The six-camera aliases use atlasSixCameraIndex, sixCameraGram, finiteCameraNaimarkGramMatrix_six_eq, and sixCameraGram_posDef.

## Scope and non-identifications

This module does not use allBasesWeylInverse, cutoffs, Dom(Y^2), halo terms, TFVD/Gpre, moments, variance, or any Weyl asymptotic expansion. It also does not assert inverse(compression) = compression(inverse): the intrinsic finite inverse is the inverse of the finite compressed block, while a future globally compressed partial inverse would be a different construction.
