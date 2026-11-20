# Native completed C3 source: the fifth Schur reduction

**State (2026-11-20):** native analytic identity PROVED in Lean; fifth-channel positivity PROVED in Lean **under exactly the third-even-source-pivot sign** already source-certified in geometry-of-numbers PR #324; the PR theorem is NOT imported into this pinned CSA checkout. All-order sign and positivity of the surviving fifth Green residual are OPEN.

## Provenance (do not reverse)

Bracket / seed / centers / legs -> Dirichlet and Genuine -> native N -> completion F(z)=A(z)N(z) -> completed normalized response -F'/F -> native vector readout `SourcePositiveReduction.sourceResponse` -> sourceReduction chain -> moments -> Hankel/Schur/Jacobi consumer.

The source is the already-formalized completed-native vector readout; **no moment-derived state is substituted**.

## Six proof modules

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

**Integration gap:** This CSA Lake dependency currently pins geometry-of-numbers at `d7cc54f5c485320f1fada33118e9e6101488819a` and does not expose PR #324's research proof as an importable module. Therefore the sign enters as an **explicit theorem argument**, not as an unproved assumption or a transplanted axiom. Reconcile the proof and its original Lean dependencies in a separate integration update.

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

The tests above were executed in the original VM checkout, all six returned exit code 0. The new branch/worktree preserves only the six proof modules and this README. Explicit `#print axioms` roots in the terminal modules report only `propext`, `Classical.choice`, `Quot.sound`. No `sorry` or `admit` was introduced.

**Next:** (1) import the finite C3 sign certificate faithfully; (2) study the fifth residual (K_5) or the source-derived next Schur pivot, never set it to zero by convention.
