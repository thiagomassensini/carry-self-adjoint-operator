# Native completed C3 source: the fifth Schur reduction

**State (2026-11-20):** native analytic identity PROVED in Lean unconditionally. The third-even-source-pivot sign is now **formally imported from GoN PR #324** via an independent leaf module and yields an **unconditional fifth positive channel** in the completed native C3 readout. The fifth Green residual and all-order positivity remain OPEN. The standard CSA Lake package still pins an older GoN revision, so the research certificate is imported by a source-rebuilding validation script (not by pretending it belongs to GoN's default public library).

## Provenance (do not reverse)

Bracket / seed / centers / legs -> Dirichlet and Genuine -> native N -> completion F(z)=A(z)N(z) -> completed normalized response -F'/F -> native vector readout `SourcePositiveReduction.sourceResponse` -> sourceReduction chain -> moments -> Hankel/Schur/Jacobi consumer.

The source is the already-formalized completed-native vector readout; **no moment-derived state is substituted**.

## Six original proof modules and the seventh integration module

1. `NativeSchurJetConvolution20261120.lean`: normalized analytic Taylor Cauchy convolution; exact z and z² shifts.
2. `SourceReductionParityStageFour20261120.lean`: native response's odd germ, oddness preserved across Schur reductions, fifth source zero at center; exact residual factor `chainWeight 5 z = z^5 * ∏_{j<5} chainAxis j z`.
3. `NativeFifthPositiveSourceGate20261120.lean`: formal fifth coefficient, positive prefactor, explicit conditional sign gate, unchanged residual.
4. `SourceFifthJetExtraction20261120.lean`: **UNCONDITIONAL** identity of each analytic axis's jets with the source S-fraction recursion; exact identification of `evenAxisJet 0 n` with canonical completed moments h_n; source Hankel minor factorizations and
   `chainScale_four_eq_native_det_ratio`.
5. `FifthNativeSourceClosed20261120.lean`: **UNCONDITIONAL**
   `chainScale_four_eq_nativeFifthScaleCandidate`, using `nativeSourceBorderedScalar_eq` (cofactor scalar) to identify the 3x3 determinant with first 2x2 determinant times its true even Schur pivot. `chainScale_four_pos_of_C3EvenThirdPivot` has an explicit sign hypothesis and no hidden positivity premise.
6. `FifthNativePositiveKernel20261120.lean`: proves the fifth-axis center is real, five-stage regularity, and
   `nativeKernel_five_positive_channels_local` from the completed two-variable Green–Wronskian response **conditional on only** `0 < sourceMomentSchur h 0 2`. Keeps the exact `chainWeight 5` source factor and `chainKernel 5` tail.

The decisive equation is (h=canonical completed native log-derivative moment):

```
chainScale 4 =
    ((h 0 * h 2 - (h 1)^2)^2 / (h 1 * h 3 - (h 2)^2)^2)
      * sourceMomentSchur h 0 2.
```

This is a theorem about the SOURCE chain, not a definition of the scale by the desired Hankel.

## Independent third-even-pivot sign

The geometry-of-numbers PR #324 (merged) contains
`research/c3-cofactor-chiral-certification/NativeEvenCertificate.lean`,
theorem `C3CofactorChiral.c3_even_third_native_pivot_positive`.
Its `nativeH` abbreviates `canonicalCompletedNativeLogDerivativeMoment`.
The proof uses the original completed C3 source's rational interval enclosures, its cofactor / Bézout transport, and is Lean-certified in that project.

**Integrated result:** `scratch_local/NativeC3EvenThirdCertificateImport20261120.lean` imports the actual `NativeEvenCertificate` research proof, not an axiom. It proves, with no additional inputs, `nativeC3_evenThirdSchur_pos`, `nativeC3_fifthChainScale_pos`, and `nativeC3_fivePositiveChannels_unconditional`.

**Source pin:** GoN PR #324 merge `6c5c97b03925c398bf77a561d6e76b14563265e0`. The imported upstream `NativeEvenCertificate.lean` has Git blob `1a032f38c0efee639a039a17d8c3694ed815114a`. The dedicated validator also rebuilds the original `SourceSchurShift`, `SourceGate`, `CofactorTransport`, and `FiniteReferenceTable` modules from this same merge.

**Build boundary:** The CSA Lake dependency still pins GoN at `d7cc54f5c485320f1fada33118e9e6101488819a`; this is intentionally unchanged. The signed theorem lives in GoN's **research tree**, outside GoN's normal library, and its research proof consumes already compiled CSA and GoN modules. The bridge is compiled as a *leaf* through `scripts/validate-native-fifth-pr324.sh`, preventing a Lake dependency cycle. The script requires the previously source-validated research prerequisite caches (from GoN's PR #324 `validate.sh`) plus GoN's main library build. It is not a hermetic build of every transitive dependency.

**Axiom audit:** The freshly compiled upstream certificate and all three leaf CSA results report only `propext`, `Classical.choice`, `Quot.sound` under `#print axioms`; no `sorry` or `admit` is introduced.

## Scope and NO-GO

This is not positivity of the complete Green kernel, because the fifth residual remains: `K_native=positivePrefix5 + conjugate(weight5(z))*weight5(w)*K5`.
Neither positive-prefix5 nor its locally exact source expansion bounds the sign of `K5`.
No all-order native Hankel positivity or RH is claimed.

No-go repository `thiagomassensini/no-go` was consulted, especially NG-023, NG-026, NG-035, NG-060 and NG-066. The construction does not identify the Cauchy–Laguerre shift square, raw material clock, or radial physical L² multiplier with the native completed source.

## Validation

From this repository root (with the normal Lake dependencies and local scratch import paths):

```bash
for f in NativeSchurJetConvolution20261120 SourceReductionParityStageFour20261120 NativeFifthPositiveSourceGate20261120 SourceFifthJetExtraction20261120 FifthNativeSourceClosed20261120 FifthNativePositiveKernel20261120; do
    lake env lean -DwarningAsError=true "scratch_local/$f.lean"
done
```

The original six-module checks each returned exit code 0. The full proof integration is reproducible from pinned upstream source blobs using:

```bash
bash scripts/validate-native-fifth-pr324.sh
```

On 2026-11-20 this command returned **`PR324_SOURCE_IMPORT_7_OF_7_PASSED`**, with warning-as-error compilation and only the standard Lean axioms. It rebuilds the five terminal GoN research modules, all six CSA construction modules, and the final seventh importing module, in a disposable temporary directory. The upstream prerequisite caches have their own original GoN source validation; this command documents but does not rebuild that entire transitive background.

**Next:** study the complete fifth residual \(K_5\) or the source-derived next Schur pivot; **do not** infer all-order positivity, and do not set that residual to zero by convention.
