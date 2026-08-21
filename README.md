# Carry Self-Adjoint Operator

Formalization of one internally derived operator chain:

```text
native log(n) evolution
  → exact head-plus-tail completed characteristic
  → even logarithmic derivative
  → moment sequence
  → Hankel Gram/shifted pair
  → projective Jacobi tower
  → height operator T = J^(-1/2)
```

The construction does not take a zero list or target heights as input.

## Current formal layer

- imports the existing maximal self-adjoint `log(n+1)` generator;
- proves its native-coordinate eigenvalue law;
- records the division-free coefficient identity `q Phi = -Phi'`;
- derives the exact logarithmic-moment recurrence used by the reference code;
- defines the finite Hankel Gram and shifted matrices;
- proves symmetry and exact principal-section compatibility.

The all-order positivity, Cholesky transport, infinite Jacobi realization,
functional calculus for `J^(-1/2)`, and characteristic/Weyl identification are
the next formal layers.  No global confinement theorem is claimed at the
current stage.

Lean is validated exclusively by the exact-checkout GitHub Actions workflow.
