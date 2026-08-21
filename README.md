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
- defines the actual camera-independent operator characteristic by removing
  the camera factor and applying the exact xi completion, with a
  cross-multiplied head-tail bridge requiring no division;
- identifies the independently constructed camera-3 bracket characteristic
  with the canonical Cp bracketed chart by analytic-continuation uniqueness;
- consequently proves `nativeScalar = genuineContinuation = riemannZeta` on
  the open critical strip and identifies the operator characteristic with the
  standard completed zeta expression there;
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
- defines the resulting canonical finite `J_N` and `T_N = J_N^(-1/2)` with
  neither a supplied whitening matrix nor target spectral heights;
- proves the transported finite Jacobi section symmetric and positive, with
  strict positivity under the corresponding injectivity hypotheses.
- defines `T_N = J_N^(-1/2)` by the Hermitian functional calculus;
- proves `T_N` exactly symmetric, so the script's numerical symmetrization is
  unnecessary in the formal construction;
- proves its characteristic polynomial has roots exactly
  `1 / sqrt(lambda_i(J_N))`, so the height spectrum is derived rather than
  supplied as input.
- proves the exact projective block law: a lower-block-triangular extension of
  the inverse whitening factor forces the old Jacobi matrix to be literally
  the upper-left block of the new one.
- proves the division-free final implication: a zero satisfying the genuine
  polarized Green identity and carrying a nonzero state is fixed by complex
  conjugation (real in the centered height variable).
- reduces that implication to the natural domain of the existing realified
  carry gamma field: only the off-axis diagonal identity with real energy
  `‖state(z)‖²` is needed, and nonvanishing is required only under the
  hypothetical off-axis condition;
- fixes the scalar boundary companion canonically to `-F'`, totalizes the
  existing carry gamma state, and transfers source nonvanishing to state
  nonvanishing by the already proved gamma injectivity;
- proves exact product and additive recomposition laws for the Green
  Wronskian, retaining every off-diagonal synthesis channel.

The direct critical-line capstone is now kernel-reduced to one concrete
construction: an enriched carry source whose totalized gamma state satisfies
the canonical off-axis diagonal Green identity for the actual completed
characteristic and is nonzero whenever that source is nonzero.  The remaining
work is to build that source while preserving diagonal TFVD, provenance,
off-diagonal synthesis, log-jet, defect, and completion channels.  The
infinite Jacobi realization and passage from finite functional calculus remain
a separate operator-completion route.  No unconditional global confinement
theorem is claimed at this stage.

Lean is validated exclusively by the exact-checkout GitHub Actions workflow.
