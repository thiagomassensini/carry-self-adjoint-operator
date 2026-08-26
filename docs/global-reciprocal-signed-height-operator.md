# Global reciprocal signed-height operator

This note records the operator obtained after the Green energy factor has been
closed.  It does not take a direct limit of the finite inverse square roots.

## 1. Closed factor and zero-mass gate

Let

```text
B : H_even → H_odd
J = B* B.
```

The repository already proves that `B` is closed and densely defined, that
`J` is positive and maximal real self-adjoint, and that every canonical finite
Jacobi section is its exact finite compression.

The range of `B` is dense without an additional hypothesis: the range still
contains the complete odd algebraic Green core.  Hence `B*` is injective.
The operator-level zero-mass condition is

```text
ker B = 0
```

The repository proves the following equivalent pair of concrete sufficient
criteria for that condition:

```text
e₀ ∈ closure(span {e₁,e₂,...})
inf_c (h₀ - 2 Σ c_n h_(n+1) + Σ c_i c_j h_(i+j+2)) = 0.
```

Either concrete criterion proves `ker B = 0` and makes the range of `B*`
dense.  Thus both inverse channels have dense natural domains.  The converse
from `ker B = 0` back to the concrete head-tail approximation is not claimed.

## 2. Canonical nonzero-support reduction

The repository now also defines the closed ambient kernel of any closed
partial real operator and its canonical support

```text
H_even^red = (ker B)^perp.
```

The restriction `B_red : H_even^red -> H_odd` is proved closed, densely
defined, and injective.  Its range is exactly the range of `B`.  Projection of
the original maximal adjoint supplies a dense formal-adjoint core, and the
maximal adjoint of `B_red` has dense range.  Therefore

```text
H_red(x,y) = ((B_red*)^-1 y, B_red^-1 x)
```

is maximal real self-adjoint on `H_even^red ⊕ H_odd` without assuming
`ker B = 0`.  The head-tail condition is needed only to identify this reduced
source with the entire even carrier.

The generic implementation is
`RealLinearPMapKernelReduction.lean`; the concrete Green and completed-native
wrappers are `closedGreenJetReducedReciprocalSignedHeightData` and
`CompletedNativeGreenWeylReducedHeightCertificate`.

The completed-native wrapper currently consumes the canonical Green-moment
kernel identity and global parity independence.  The completed projective
TFVD carrier already supplies all-order independence.  Instantiating the
wrapper on that carrier still requires the exact Gram identification between
its parity jets and the canonical logarithmic moments.  The normalized radial
Taylor carrier is not a substitute: its first odd complex jet vanishes by the
existing differentiability obstruction.

## 3. Full-carrier signed reciprocal block

Define on `H_even ⊕ H_odd`

```text
H(x,y) = (B⁻¹ y, (B*)⁻¹ x).
```

Lean first proves the general inverse-adjoint identity

```text
(T⁻¹)* = (T*)⁻¹
```

for closed densely defined injective channels with the required dense ranges.
Consequently the two off-diagonal entries of `H` are mutual maximal adjoints.
The bundled theorem
`closedGreenJetReciprocalSignedHeightOperator_isMaximalRealSelfAdjoint`
then states literal equality with the maximal real adjoint.  Closedness follows
from the closed graph of that adjoint.

For an arbitrary ambient realization, `completedGreenJet` promotes the data
to `UniformSpace.Completion E` first.  Gram representation and both parity
independence statements are preserved.  The resulting
`canonicalCompletedGreenJetMomentReciprocalSignedHeightOperator` therefore
requires no completeness hypothesis on the original ambient space.

## 4. Exact relation to the Jacobi operator

For every `x` in the natural domain of `J=B*B`, Lean constructs both required
domain witnesses and proves

```text
(Jx, 0)  ↦[H]  (0, Bx)  ↦[H]  (x, 0).
```

This is `LinearPMap.realReciprocalOffDiagonal_apply_secondSquareInput`.
It identifies the first channel of `H²` with `J⁻¹` on `range J`, without an
external extension and without an unbounded Borel functional calculus.

## 5. Spectral frontier

The exact finite TFVD head-plus-tail identities and the Hilbert
head-in-shifted-tail approximation remain different statements.  They affect
whether the full even carrier equals the reduced support, but no longer block
the reduced maximal self-adjoint operator or its completed resolvent limit.

Once the projective TFVD Gram identification instantiates the concrete
reduced certificate, the spectral identification is a separate theorem: one
must identify the nonzero spectrum of the reduced signed-height operator with
all Genuine zero heights.  Self-adjointness by itself does not establish that
identification.
