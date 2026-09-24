# Multibase readout → height point spectrum bridge

## Goal

This checkpoint connects the already formalized multibase/mixed-return readout
to the already formalized self-adjoint height spectrum.  It deliberately does
**not** construct a second height operator.

The repository already contains both ends:

1. `MixedReturnNativeReadout.lean` proves, for every six-camera cutoff,

   ```text
   mixedReturnCompletedHeightCharacteristic cutoff t
     = completedNativeOperatorCharacteristic t
   ```

   on the full real height axis.

2. `CompletedNativeJacobiCyclicAtomicExtraction.lean` and
   `CompletedNativeJacobiPointSpectrumConverse.lean` prove that a zero of
   `completedNativeOperatorCharacteristic` gives genuine point spectrum,
   including the reduced signed-height operator whose eigenvalue is the height
   itself.

## Exact interface

The module `MixedReturnHeightSpectrumBridge.lean` introduces only

```lean
def IsExactCompletedNativeHeightReadout (readout : ℝ → ℂ) : Prop :=
  ∀ t : ℝ, readout t = completedNativeOperatorCharacteristic (t : ℂ)
```

This is intentionally tiny.  Any future realization—minimal multibase
characteristic, Potapov factor, boundary/Weyl readout, or a rigorously promoted
cutoff limit—only needs to prove this equality to inherit the existing spectral
route.

## Zero-equivalent interface

The companion module
`MixedReturnHeightZeroEquivalenceBridge.lean` records the strictly weaker
interface needed by the *spectral* handoff:

```lean
def IsZeroEquivalentCompletedNativeHeightReadout
    {A : Type*} [Zero A] (readout : ℝ → A) : Prop :=
  ∀ t : ℝ,
    readout t = 0 ↔
      completedNativeOperatorCharacteristic (t : ℂ) = 0
```

The codomain is deliberately not restricted to `ℂ`.  A physical multibase
characteristic may remain vector-valued, or a matrix-valued residual may stay
matrix-valued, until its own zero condition has been proved to mean collective
blindness.  The new interface can then hand that zero condition directly to the
already existing signed-height and Jacobi theorems.

For a scalar reduced secular/Potapov readout, the module supplies the standard
constructor

```text
readout(t) = unit(t) * completedNativeOperatorCharacteristic(t),
unit(t) != 0
---------------------------------------------------------------
same real-height zero locus.
```

It also supplies the right-factor variant.  This is exactly the pattern
already used by `NativeCarrySpectralWeyl.Camera.CommonZeroSet`: a nonvanishing
camera factor gives equality of zero sets, while local zero multiplicity is
kept as a separate question.

This distinction is intentional:

```text
literal equality       -> derivatives, Taylor coefficients, moments,
                          and multiplicity-sensitive arguments;
zero equivalence       -> the point-spectrum handoff only.
```

Thus `mixedReturnCompletedHeightCharacteristic` has both interfaces: its
already-proved literal equality induces zero equivalence, but the new
interface lets a future physical multibase/Potapov realization stop as soon as
it proves the correct real-axis collective zero condition.

## Concrete consequences

For the already existing six-camera mixed-return realization:

```text
mixed-return readout zero at t
  -> completedNativeOperatorCharacteristic(t)=0
  -> reduced signed-height point eigenvalue t
```

and, for `t ≠ 0`,

```text
mixed-return readout zero at t
  <->
positive Jacobi point eigenvalue (t^2)^(-1).
```

No new positivity, no zero table, no numerical fitting, and no extra
self-adjoint extension is used.

## Why this is the right formal seam for the new research

The recent minimal-characteristic/Potapov experiments should not rebuild the
Jacobi/height machinery.  Their formal obligation is upstream and narrower:

```text
new multibase characteristic
  -> exact real-axis readout identity
  -> IsExactCompletedNativeHeightReadout
  -> existing zero ↔ point-spectrum chain.
```

This keeps the new work non-circular and makes the proof dependency explicit.

## Next formal gates

The next modules should be staged separately:

1. **Finite minimal realization.**
   Formalize the input isometry, camera coisometry, controllable/observable
   reduction and completion-independence.  Do not mention heights.

2. **Root-free secular identity.**
   Formalize the fixed-reflection active defect and prove its real-axis zero
   condition is equivalent to the exact multibase readout zero.

3. **Cutoff limit.**
   Formalize local-uniform convergence of the de-normalized physical
   characteristic on a strip.  Keep this separate from point spectrum.

4. **Limit readout identification.**
   Only after the limit characteristic has been identified with the canonical
   completed-native characteristic *or proved zero-equivalent to it on the
   real axis* should the present bridge be applied.  Equality remains necessary
   if the next result uses coefficients or derivatives rather than only zeros.

5. **Global spectral completeness.**
   This remains a distinct theorem: the current repository already proves
   point-spectrum equivalence for the canonical characteristic under the HP
   carrier certificate, but that does not by itself prove a new global
   Cartwright/de Branges factorization.

## CI note

This work is kept on a non-`main` branch and no pull request is opened.  The
repository-wide Lean workflow runs on pushes to `main` and on pull requests,
so this checkpoint is intentionally left for local `lake build` validation
while GitHub Actions billing is unavailable.
