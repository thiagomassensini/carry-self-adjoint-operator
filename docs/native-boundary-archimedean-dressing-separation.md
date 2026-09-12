# Native boundary versus archimedean dressing

This branch starts at `ec81ba267261307e83ac49bb9ee6de6485947904` and records
the boundary-chart separation without reopening the completed cancellation
carrier or the raw Gamma sewing gate.

The two scalar completions are distinct:

* the carry/C3 head-plus-tail completion is the exact geometric construction
  that produces the native scalar `nativeHeightScalar`;
* the operator characteristic is the product
  `completedNativeOperatorCharacteristic z =
  nativeXiCompletionFactor z * nativeHeightScalar z`.

No camera limit, Hankel construction, Jacobi argument, or HP argument is used
here.

## Native chart

The native undressed chart is

[
 B_{
m native}(z)=
 igl(-N'(z),N(z)igr)
]

with

[
 N(z)=\texttt{nativeHeightScalar}(z)
     =\texttt{nativeScalar}(\texttt{operatorHeightParameter}(z)).
]

In Lean this is
`canonicalNativeUndressedScalarBoundaryPair`.  On the genuine strip it is
literally the already existing normalized TFVD trace:

[
(-N'(z),N(z)) =
(\texttt{normalizedLogJetTailReadout}(z),
 \texttt{normalizedValueTailReadout}(z)).
]

This is proved by
`canonicalNativeUndressedScalarBoundaryPair_eq_normalizedTfvdTrace`, using
the existing value and log-jet crosswalks.

## Archimedean dressing

Put

[
 A(z)=\texttt{nativeXiCompletionFactor}(z),
 \qquad A_c(z)=-A'(z).
]

The triangular dressing is

[
 {\cal D}_A(z)(p,q)
   =igl(A(z)p+A_c(z)q,;A(z)qigr).
]

The theorem
`canonicalCompletedC3ScalarBoundaryPair_eq_nativeArchimedeanBoundaryDressing`
proves, on the genuine strip,

[
(-F'(z),F(z))={\cal D}_A(z)(-N'(z),N(z)).
]

The product identity
`completedNativeOperatorCharacteristic_eq_nativeXiCompletionFactor_mul_nativeHeightScalar`
is definitional, and
`completedNativeOperatorBoundaryCompanion_eq_product` supplies the first
coordinate.  Thus the product rule is exact and no normalization is fitted.

## Green-form correction

Define

[
G_N(z,w)=
operatorname{greenForm}(B_{
m native}(z),B_{
m native}(w)).
]

The theorem
`canonicalNativeUndressedGreenForm_eq_nativeWronskian` identifies it with
the native scalar Wronskian, with the argument order used by the existing
boundary bridge.

The completion-jet cross correction is

[
 C_A(z,w)=
 igl(overline{A(z)}A_c(w)-overline{A_c(z)}A(w)igr)
 overline{N(z)}N(w).
]

The theorem
`canonicalCompletedC3ScalarGreenForm_eq_scaledNative_add_archimedeanCorrection`
proves the exact identity

[
G_F(z,w)=
 overline{A(z)}A(w),G_N(z,w)+C_A(z,w),
]

where (G_F) is the Green form of the existing scalar pair
((-F',F)).  The derivative spelling is
`canonicalArchimedeanBoundaryGreenCorrection_eq_derivative`.

For a direct comparison with the undressed chart, the full transport
correction is

[
 T_A(z,w)=
 igl(overline{A(z)}A(w)-1igr)G_N(z,w)+C_A(z,w).
]

The theorem
`canonicalCompletedC3ScalarGreenForm_eq_native_add_archimedeanTransportCorrection`
proves (G_F=G_N+T_A).

## Exact residual classification

Let (G_Gamma(z,w)) be the existing Gamma boundary Green form.  The branch
does not claim that this form equals the native chart: no such identification
is present in the current formalization, and the existing Gamma-versus-native
audits keep that seam open.

Two equivalent residual decompositions are available.

With the direct native residual

[
 R_{Gamma,N}(z,w)=G_Gamma(z,w)-G_N(z,w),
]

the theorem
`canonicalCompletedC3RawGammaWronskianDefect_eq_gammaNativeMismatch_sub_archimedeanTransportCorrection`
proves

[
 \texttt{rawGammaWronskianDefect}(z,w)
 =
 R_{Gamma,N}(z,w)-T_A(z,w).
]

Equivalently, with the scaled-native residual

[
 widetilde R_{Gamma,N}(z,w)
   =G_Gamma(z,w)-overline{A(z)}A(w)G_N(z,w),
]

the theorem
`canonicalCompletedC3RawGammaWronskianDefect_eq_nativeMismatch_sub_archimedeanCorrection`
proves

[
 \texttt{rawGammaWronskianDefect}(z,w)
 =
 widetilde R_{Gamma,N}(z,w)-C_A(z,w).
]

The existing theorem
`canonicalC3NativeBoundaryGreenMismatch_eq_zero_iff` gives the exact
zero criterion for the scaled residual.  No scalar manipulation is used to
declare either residual zero.

The correct status is therefore Outcome C: the archimedean dressing
correction is completely explicit, while the current Gamma boundary chart has
not yet been identified with the native undressed chart.  The old raw defect
is exactly the difference of these two independently defined pieces.  Existing
near-center non-sewing results show that the old defect is not silently
discarded; they do not identify the two summands separately.

## Scope and provenance

* The native pair is built from `nativeScalar`, the centered height
  parameter, and existing TFVD normalized value/log-jet theorems.
* The dressed pair is the existing completed operator boundary pair.
* The product Green theorem is reused through
  `completedGreenWronskian_mul`; provenance or boundary channels are not
  replaced by a positive proxy.
* No new boundary carrier is introduced.
* No equality with the Gamma boundary form is asserted.
* No Hankel, Jacobi, HP, zero, zeta, RH, camera, cutoff, or atlas-limit
  theorem is used.

## Public declarations

The focused module is
`CarrySelfAdjointOperator/NativeBoundaryArchimedeanDressingSeparation.lean`.
Its load-bearing audit is
`CarrySelfAdjointOperator/NativeBoundaryArchimedeanDressingSeparationAudit.lean`.
