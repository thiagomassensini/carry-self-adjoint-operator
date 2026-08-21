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
- names the exact finite-head-plus-whole-center-tail characteristic and proves
  it equals the common dressed native scalar independently of cutoff;
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
- proves that the exact whitening identity itself forces `B_N` to act
  injectively, so injectivity is not a separate numerical input;
- constructs a canonical exact whitening from Mathlib's LDL/Gram--Schmidt
  decomposition, proves its diagonal normalization and lower-triangularity;
- proves the transported finite Jacobi section symmetric and positive, with
  strict positivity under the corresponding injectivity hypotheses.
- defines `T_N = J_N^(-1/2)` by the Hermitian functional calculus;
- proves its characteristic polynomial has roots exactly
  `1 / sqrt(lambda_i(J_N))`, so the height spectrum is derived rather than
  supplied as input.
- proves the exact projective block law: a lower-block-triangular extension of
  the inverse whitening factor forces the old Jacobi matrix to be literally
  the upper-left block of the new one.

Constructing those two Gram representations from the completed native-carry
Green/gamma identity, constructing the compatible lower-triangular Cholesky
whitening tower, the infinite Jacobi realization,
passage from the finite functional calculus to the infinite operator, and
characteristic/Weyl identification are the next formal layers.  No global
confinement theorem is claimed at this stage.

Lean is validated exclusively by the exact-checkout GitHub Actions workflow.
