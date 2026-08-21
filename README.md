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
- identifies the exact Green/gamma output needed for all-order positivity as
  one Hilbert-space Gram representation of each moment kernel;
- proves positive semidefiniteness at every order, and positive definiteness
  whenever the corresponding finite feature prefix is linearly independent.
- defines the exact whitening transport `J_N = B_N K_N B_Nᵀ` used by the
  reference script (`B_N = L_N⁻¹` for Cholesky whitening);
- proves the transported finite Jacobi section symmetric and positive, with
  strict positivity under the corresponding injectivity hypotheses.

Constructing those two Gram representations from the completed native-carry
Green/gamma identity, constructing compatible Cholesky whitenings at all
orders, the infinite Jacobi realization,
functional calculus for `J^(-1/2)`, and characteristic/Weyl identification are
the next formal layers.  No global confinement theorem is claimed at this
stage.

Lean is validated exclusively by the exact-checkout GitHub Actions workflow.
