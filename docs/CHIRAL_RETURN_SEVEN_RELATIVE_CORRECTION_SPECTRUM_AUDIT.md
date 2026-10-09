# Complete storage correction: fixed-dimension relative control and N=7 spectrum

## Checkpoint and statuses

Audited published main: `45cf224813a4a786832ae7f14d755860fc48452b`.
HEAD, main and origin/main agreed; the preceding pull was already up to date.
The pre-existing untracked `C2OddTfvdTransport.lean` and its audit are preserved
and excluded from staging. Earlier reports are not rewritten.

- `PASS_SEVEN_COMPLETE_STORAGE_RELATIVE_CONTROL`
- `PASS_SEVEN_FIRST_CORRECTION_RELATIVE_SPECTRUM`
- `PASS_FIXED_DIMENSION_QUADRATIC_RELATIVE_CONTROL`

No arbitrary-N source positivity or dimension-uniform radial radius is claimed.

## Quantifiers: A is sufficient

The two statements are different:

\[
\mathrm A:\quad \forall N\;\exists h_N>0\;\forall h\in(0,h_N),\quad S_{N,h}>0,
\]

\[
\mathrm B:\quad \exists h_0>0\;\forall N\;\forall h\in(0,h_0),\quad S_{N,h}>0.
\]

A suffices for positivity at every fixed finite order. It is unnecessary to
prove B first. Compactness of a fixed finite unit sphere proves a threshold
for that dimension; it does not justify exchanging these quantifiers.
In the discrete radial grid this means `forall N, eventually k, forall c`,
with the eventual index permitted to depend on N.

## Complete correction and its provenance

The same fully synthesized completed value/companion in the original Cauchy
carrier is reused. Set

\[
E_7(x)=\texttt{nativeSourceSevenBoundaryEnergy}(x),\qquad
S_R(h,x)=\texttt{radialSevenRegularizedStorage}(R,h,x).
\]

The source's own analytic remainder R is retained. The previously proved
identity between actual storage and S_R is applied only after complete vector
synthesis. Every ordered i/j cross, all higher reconstructed Euler coordinates
and the entire analytic remainder remain present.

New homogeneity theorems follow from those same formulas. Joint continuity,
`S_R(0,x)=E_7(x)` and the old certified source coercivity give

\[
\forall\eta>0\;\forall^{\infty}_{h\to0}\;\forall x,\qquad
|S_R(h,x)-E_7(x)|\le\eta E_7(x).
\]

This is a bound on the COMPLETE correction as a sum. It does not take a
potentially wasteful sum of independently bounded cross terms. It includes
both the finite-prefix correction and the analytic remainder. On the actual
radial sequence, the kernel also proves

\[
(1-\eta)E_7(x)\le \operatorname{Re}S_k(\text{normalized input}(h_k,x),1)
\le(1+\eta)E_7(x).
\]

For any chosen `0 < eta < 1`, this retains a strictly positive fraction of
the boundary margin. No amplitude, camera or inner product is changed.

## General finite-dimensional analytic lemma

`fixedFiniteQuadratic_relative_control` works for any fixed n and a complete
quadratic readout S(h,x). Its explicit premises are:

- joint continuity at every (0,x);
- degree-two scalar homogeneity;
- equality S(0,x)=E(x);
- an already-certified coercivity `epsilon * norm(x)^2 <= E(x)`.

`fixedFiniteQuadratic_positive_radius` concludes `exists delta > 0` AFTER n
is fixed. These are general analysis theorems, not new assumptions supplied
to a concrete positivity theorem. Their N=7 instantiation discharges every
premise from existing source declarations. For other N, source coercivity
still requires its own geometric proof. No Hankel positivity is an input.
The finite Pi norm serves only as a compactness/coordinate tool; it does not
replace the Cauchy metric in the actual storage.

## First correction: exact quadratic form

Write `c_j = nativeSourceOddBoundaryCoefficient j`. These are raw source
Taylor coefficients, not a definition using canonical moments.
The previous full-storage derivative is reused, including its proof that
source parity makes the analytic remainder's first contribution zero:

\[
L_7(x)=112\operatorname{Re}\bigl(
\overline{-c_4x_1+c_5x_3-c_6x_5}\,x_6\bigr).
\]

Only the final even coordinate couples to one functional of the odd sector.
In parity order `(x0,x2,x4,x6,x1,x3,x5)`, the certified boundary matrix is
`E = diag(2A,2B)`, where

\[
A=\begin{pmatrix}
c_0&-c_1&c_2&-c_3\\
-c_1&c_2&-c_3&c_4\\
c_2&-c_3&c_4&-c_5\\
-c_3&c_4&-c_5&c_6
\end{pmatrix},\qquad
B=\begin{pmatrix}
c_1&-c_2&c_3\\
-c_2&c_3&-c_4\\
c_3&-c_4&c_5
\end{pmatrix}.
\]

The correction matrix H has only entries
`H34=H43=-56c4`, `H35=H53=56c5`, `H36=H63=-56c6`.
`nativeSourceSevenBoundaryMatrix_quadratic` and
`radialSevenFirstCorrectionMatrix_quadratic` prove these matrices expand the
EXISTING source forms on complex coefficients. This is an algebraic analysis
of the old metric, not a new moment Gram or a fitted operator.

## Exact spectrum relative to the certified energy

Let D5, D6 and D7 be the existing five-even, six-odd and seven-even source
discriminants. All three were already certified positive from raw source
integrals. Let `v=(-c4,c5,-c6)` and let
`K = radialSevenOddCouplingCofactor`, the explicit polynomial cofactor.
Algebraically it is `v^T adj(B) v`; the new kernel identity instead evaluates
it directly in the already-existing odd square-completion coordinates:

\[
K=D_6\beta,\quad
\beta=\frac{d^2}{a}+\frac a\delta\nu^2+\frac\delta{D_6}\omega^2>0,
\]

where `a=c1`, `b=c2`, `c=c3`, `d=c4`, `e=c5`, `f=c6`,
`delta=a*c-b^2`, `nu=e-b*d/a`, and
`omega=-f+c*d/a-((b*c-a*d)/delta)*nu`.
Strictness uses the previously certified `c4 > 0`, not a new sign premise.

Define the positive source-derived relative radius

\[
\kappa_7=28\sqrt{\frac{D_5K}{D_7D_6}}.
\]

The kernel computes the complete pencil:

\[
\det(H-\lambda E)=128D_7D_6\lambda^5
(\kappa_7^2-\lambda^2).
\]

`radialSevenFirstCorrection_relative_spectrum` proves its real singular
parameters are EXACTLY `0`, `+kappa7`, `-kappa7`. The factorization records
five zero modes and two simple nonzero roots. This is a relative matrix
pencil; no new global material/spectral operator is constructed.

The familiar sharp Rayleigh estimate `|L7(x)| <= kappa7 * E7(x)` follows
mathematically from this symmetric positive-energy pencil, but a separate
Lean theorem asserting that sharp estimate is NOT added here. The complete
storage relative estimate above is independently kernel-checked and does
not rely on that inference. Likewise, this turn does not assert a uniform
first-order remainder estimate `o(h) E7` across all directions.

## How the structure may extend in N

The existing `ChiralReturn.radialEulerPower_green_boundary` already retains
all ordered boundary crosses at every degree and every finite N. A general
N-node boundary chart and source margin still have to be supplied; only the
N=7 chart and certified margin are instantiated in this turn.

As a mathematical derivation, not a new Lean capstone, interpolation on
nodes 1,...,N predicts the first higher boundary jet
`B_N = (N*(N+1)/2) h x_(N-1) + O(h^2)`. Inserting this in the existing signed
Green tower predicts

\[
L_N(x)=4\frac{N(N+1)}2
\sum_{\substack{j<N\\2j\ge N}}
(-1)^{j+N}c_j\operatorname{Re}
(\overline{x_{2j-N}}x_{N-1}).
\]

This predicts another opposite-parity coupling of rank at most two. It
reproduces exactly the kernel-checked N=7 correction. The general formula
and its sharp relative radius have NOT been formalized in this checkpoint.
In particular, the explicit growth of the node sum does not by itself
prove either boundedness or divergence of relative radii across N: the
source energy and its dual geometry must also be controlled.

## Remaining frontier

For claim A, generalize the COMPLETE boundary chart in N and certify each
source boundary energy as coercive. The analytic relative-control lemma is
now available once those concrete premises are discharged. The decisive
source sign frontier remains arbitrary-order coercivity from the raw source;
N=7 alone cannot establish it. Claim B would require additional estimates
on these relative corrections and thresholds uniformly in N. It is not a
prerequisite for A and is neither proved nor refuted here.

## Axioms, validation and files

The four dedicated audits use `#assert_prime_depth_source_axioms`,
`#print axioms` and transitive `#assert_oriented_green_source` checks.
Canonical moments, HP/Stieltjes, Hankel, Jacobi/height, Herglotz and BR2
are forbidden in the new capstone dependency closures. Allowed footprint:
`[propext, Classical.choice, Quot.sound]` or a subset.

New modules (each has a dedicated Audit module):

- `FiniteQuadraticRelativeControl`
- `CompletedNativeChiralReturnSevenRelativeControl`
- `CompletedNativeChiralReturnSevenRelativeSpectrum`
- `CompletedNativeChiralReturnSevenRelativeRadius`

The public capstones are imported by the main library and
repository audit umbrella. README receives an appended checkpoint; no
previous research report is overwritten.

Validation commands and exact exit outcomes are recorded in
`research/chiral-seven-relative-correction-2026-10-08/validation-summary.txt`.
They include the new module/audit builds with `--wfail`, direct Lean audit
execution, full library and Audit builds, both repository audit scripts,
placeholder scans and `git diff --check`. Remote execution is on llm.
GitHub Actions status is tracked separately from these kernel executions.
The pre-existing two untracked user files remain outside the published change.
