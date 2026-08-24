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
- proves that the unit centered bracket is an exact causal recurrence, gives
  its double-telescoping all-order reconstruction, and establishes uniqueness
  of the compatible state before any positivity or admissibility condition is
  imposed;
- identifies every causal unit cell from depth two onward inside the natural
  all-bases camera atlas, so four low coordinates and the first unit bracket
  of each natural camera determine the complete state;
- proves exact center/leg lattice separation: aligned centers are multiples of
  the camera slope, while neither emitted leg is; for natural cameras this is
  nondivisibility by the base itself, and the exceptional C2 legs are odd;
- computes the complete residue ledger `(center,left,right) = (0,d-r,r)`
  modulo the camera slope `d`, and proves that the two leg classes coincide
  exactly for the antipodal radius `2r=d`;
- packages those channels in `ZMod d`, proves that cyclic reflection fixes the
  center and swaps the literal legs, separates the center singleton from every
  leg orbit, and computes that orbit's exact one-or-two cardinality;
- lifts cyclic reflection to an isometric symmetric involution on the full
  Euclidean residue-signal space, constructs its complementary orthogonal
  even/odd projections, and proves that the centered bracket is even while
  the oriented leg difference is odd;
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
- proves that continuity removes the apparent real-axis Green diagonal
  ambiguity: the normalized state norm is forced to equal the derivative of
  the scalar response at the collision point;
- proves continuity of the literal finite C3 Hilbert coordinate and derives
  the same center-diagonal law for the concrete two-channel product ledger;
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
- constructs the canonical signed realization `H_N = T_N ⊕ (-T_N)`, proves
  exact symmetry and sector-factorization of its characteristic polynomial,
  and proves that the symmetric sector swap satisfies `S H_N S = -H_N`;
- constructs the canonical finite Green-jet/signed-height intertwiner
  `B_N = U_N diag(B_N^G, T_N B_N^G)`: it simultaneously whitens the full
  parity Gram `diag(G_N,K_N)` and converts the Green even/odd grading into
  the signed-sector reflection, in both analysis and adjoint forms;
- promotes the compatible finite signed tower to the closed Hilbert span of
  the Green jets, proves that the closed odd sector is exactly the orthogonal
  complement of the closed even sector, and constructs the resulting global
  bounded self-adjoint parity reflection `R = 2 P_even - I`;
- proves the exact finite/global law `R V_N = V_N S_N` at every order and its
  compatibility with every cutoff inclusion, so this reflection is one
  cutoff-independent Hilbert operator rather than a family of fitted maps;
- constructs the algebraic Green energy factor `B₀ e_n = o_n` and reverse
  shift `C₀ o_n = e_(n+1)`, derives their formal-adjoint law from the exact
  shifted moment relation, and proves that the dense reverse-shift domain
  forces `B₀` to be closable;
- defines the canonical graph closure of `B₀`, proves it closed, contains the
  algebraic factor, and retains the original algebraic domain as a core;
- defines the maximal real adjoint directly on its represented-functional
  domain and proves the closed-graph resolvent theorem
  `(I + B* B)x = f` for every `f`;
- constructs the canonical infinite positive operator `J = B* B`, proves it
  densely defined, closed, and literally equal to its maximal adjoint after
  Hilbert completion, with the exact core inclusion `J₀ ≤ J`;
- proves that every canonical finite Jacobi section is the exact compression
  of this same self-adjoint `J`, so the projective matrix and operator tower
  agree on every finite cylinder;
- proves `ker (B* B) = ker B` and identifies trivial kernel of the closed
  factor exactly with closability of the algebraic inverse `B₀⁻¹`;
- reduces a sufficient zero-spectral-mass condition to one literal
  head--tail completion gate: `e₀` must belong to the closure of
  `span {e₁, e₂, ...}`; this final approximation is not assumed to follow from
  finite Hankel positivity;
- rewrites that head--tail gate exactly as a moment-only limit: for finite
  coefficients `c`, the squared error is
  `h₀ - 2 sum c_n h_(n+1) + sum c_i c_j h_(i+j+2)`, and arbitrarily small
  values of this explicit quadratic defect force `ker J = 0` without a zero
  list or an atomic measure model;
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
- proves the exact normalization bridge from the existing realified gamma
  identity to the completed complex Green identity: the completed Wronskian
  must equal `-2i` times the concrete all-bases Cauchy skew; from that literal
  scalarization equation Lean derives the canonical gamma-state energy law;
- packs every coordinate of the two-leg, three-cell complex C3 port into the
  literal six-camera family `2, ..., 7`, using separate real and imaginary
  Hilbert channels, and proves that this all-bases camera source is injective
  and therefore nonzero throughout the open strip;
- separates faithful coordinate storage from Green transport: after proving
  that the raw real/imaginary split is not an intrinsic Green intertwiner, it
  constructs the corrected symplectic packing `(x1,x2) -> (-R x1,R x2)` into
  the global camera Hilbert space and proves its ambient skew is exactly
  `re(greenForm x y)`;
- promotes that corrected packing through the coordinatewise Naimark
  isometry without loss, proves the resulting global state is injective and
  nonzero in the open strip, and recovers the exact radial factorization and
  its zero criterion `re s = 1/2` in the ambient Hilbert space;
- proves exact product and additive recomposition laws for the Green
  Wronskian, retaining every off-diagonal synthesis channel, and proves that
  at a zero of the scalar factor the completion-jet channel vanishes rather
  than cancelling an independently retained provenance term.
- realizes the product rule before scalar projection by the canonical
  weighted Hilbert direct sum `G(z) a_z ⊕ A(z) g_z`, and proves that its
  nonzero second-factor provenance survives completion whenever `A(z) ≠ 0`;
- equips the two-leg complex C3 port with its canonical `L²` product wrapper,
  preserving every cell and both legs while supplying the Hilbert norm
  required by the completed direct-sum ledger;
- specializes that state ledger to the actual xi factor, native scalar, and
  canonical enriched C3 port, proving that at every open-strip zeta zero the
  completed scalar characteristic is zero while the full product ledger is
  still nonzero;
- states the remaining off-axis Green identity directly on that concrete
  two-channel ledger and proves that this single identity closes critical-line
  confinement without a separate state-nonvanishing hypothesis;
- specializes that product ledger to the actual xi-completed native
  characteristic, proves holomorphy of both factors on the open strip, and
  identifies its canonical companion `-F'` with the exact product companion,
  proves the xi factor is nonzero there, and includes the specialization
  stated directly at every `riemannZeta` zero;
- specializes the complete provenance-preserving C3 port to the actual
  operator coordinate, proves that this enriched state is nonzero everywhere
  in the open critical strip, and proves that its tail-completed scalar
  readout is the camera-3 factor times `riemannZeta`;
- keeps its native direct/reflected Green pairing explicit instead of assuming
  a complex inner-product structure that this C3 carrier does not possess;
- proves that this enriched source is literally the existing complete C3
  Genuine Green boundary pair, and that its direct/reflected Green bulk has
  the exact radial factorization and vanishes in the open strip exactly at
  `re s = 1/2`;
- proves that the raw complex C3 bulk cannot itself equal a scalar diagonal
  Wronskian off the critical line: the Wronskian is purely imaginary while
  the bulk has nonzero real part;
- extracts the correctly typed positive radial C3 energy using the exact
  continuous cofactor of the tilt, and proves
  `(z - conj z) * energy = -2i * re(C3 bulk)` in centered coordinates;
- constructs the ordinary and log-jet all-cutoff C3 states in `l2`, proves
  norm convergence of both finite-prefix channels, and identifies the raw
  finite gamma kernel with their completed Gram pairing;
- transports the causal C3 bracket and Genuine Green pair to that same
  completed state while retaining radial, provenance, off-diagonal, seam,
  residual, and completion channels as separate data;
- polarizes the construction at independent spectral parameters, applies the
  exact height-coordinate rotation and xi/chart product rule, and proves that
  the six-channel final readout is the completed `(F,-F')` Wronskian at every
  cutoff before the nonzero chart weight is divided out;
- proves that only the independent head-tail correction automatically tends
  to zero: the retained provenance/off-diagonal/residual triple converges to
  `raw Wronskian - radial Green`;
- specializes that limit at a Genuine zero and proves the structural triple
  tends to `-radial Green`, hence tends to zero exactly when `re s = 1/2` and
  cannot tend to zero at a hypothetical off-critical Genuine zero;
- restates the final capstone with no abstract state or extra nonvanishing
  premise using this positive radial energy.

The direct critical-line capstone is now reduced to one correctly typed
global kernel identification.  The complete mixed ledger and its `(F,-F')`
readout are closed, but its structural triple is not a disposable completion
tail: at a Genuine zero its vanishing is equivalent to the critical-line
conclusion.  The raw complex bulk and raw-coefficient renaming are both
formally ruled out as shortcuts.  The correctly rotated positive Green form
is now transported injectively through the global camera completion and
Naimark realization with exact skew preservation.  The remaining noncircular
step is to identify that concrete global skew with the completed Wronskian
while preserving every channel until its local final readout.  The infinite
self-adjoint Jacobi realization is now constructed; passage to its
inverse-square-root height operator and the final spectral identification
remain a separate operator-completion route.  No unconditional global
confinement theorem is claimed at this stage.

Lean is validated exclusively by the exact-checkout GitHub Actions workflow.

The structural derivation of the causal reconstruction theorem is recorded in
[`docs/causal-bracket-state-uniqueness.md`](docs/causal-bracket-state-uniqueness.md).
The cyclic center/leg channel decomposition is recorded in
[`docs/bracket-residue-reflection-orbit.md`](docs/bracket-residue-reflection-orbit.md).
The finite reflection-to-signed-height construction, its exact transported
cutoff cocycle, and the resulting complete metric and canonical Hilbert
carriers are recorded in
[`docs/canonical-green-jet-signed-height-intertwiner.md`](docs/canonical-green-jet-signed-height-intertwiner.md).
The closed-span Hilbert promotion and its dense compatible finite tower are
recorded separately in
[`docs/green-jet-signed-height-hilbert-space.md`](docs/green-jet-signed-height-hilbert-space.md).
The global closed-sector decomposition, self-adjoint parity reflection, and
its exact finite/cutoff restrictions are recorded in
[`docs/green-jet-parity-reflection.md`](docs/green-jet-parity-reflection.md).
The exact shifted-moment adjoint law, closability proof, and the distinction
between graph closure and circular provenance are recorded in
[`docs/green-jet-energy-factor-closability.md`](docs/green-jet-energy-factor-closability.md).
The completed C3 module map, six-channel sewing identities, exact structural
limit, and remaining noncircular Green--Wronskian gate are recorded in
[`docs/completed-c3-green-wronskian-frontier.md`](docs/completed-c3-green-wronskian-frontier.md).
