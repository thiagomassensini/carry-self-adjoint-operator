# Completed C3 symplectic collision variation audit

## Scope

This audit tests the already existing crossed-chart and global Green
operator carriers at the central collision.  It does not introduce an
abstract xi state, a factorwise Green representation, a positive replacement
for a symplectic form, or an all-order construction.

The Lean implementation is
`CarrySelfAdjointOperator/CompletedC3SymplecticCollisionVariationAudit.lean`.

## 1. The division-free collision closes exactly

Centered evenness gives

\[
W_{(F,-F')}(0,0)=0.
\]

Specializing `completedFNegFPrimeWronskian_crossedChartIdentity` before any
division therefore gives

\[
 |A(0)|^2 W_{\mathrm{raw}}(0,0)
 + \mathcal A_{\mathrm{arch/chart}}(0,0)=0.
\]

This is the theorem
`canonicalCompletedC3RawArchimedean_center_collision_cancel`.

The cancellation is also operatorial.  The weighted raw term is the existing
boundary symplectic form

\[
 \left\langle A(0)X_{\mathrm{raw}}(0),
 J_{\partial}\,A(0)X_{\mathrm{raw}}(0)\right\rangle,
\]

and the archimedean/chart term is

\[
 \left\langle X_{\mathrm{arch}}(0),
 J_{\mathrm{arch}}X_{\mathrm{arch}}(0)\right\rangle.
\]

Their exact sum is zero in
`canonicalCompletedC3CentralCollision_symplecticForms_cancel`.  Neither
summand is asserted to be a positive Gram.

The global response state itself is nonzero at the collision.  Its radial
block contains the nonzero completed C3 ordinary-gradient state, multiplied
by the nonzero completion factor.  Thus the zero total flux is cancellation
of symplectic forms, not disappearance of the state.

## 2. The current global carrier is not the complete collision carrier

On the fixed-center real line, with source `z=t` and response `w=0`, the
mixed radial coefficient is identically zero:

\[
 c_{\mathrm{rad}}(s(t),s(0))=0.
\]

Consequently

\[
 K_{\mathrm{global}}(t,0)
 =\mathcal A_{\mathrm{arch/chart}}(t,0),
\]

both as a scalar kernel and as the bounded-operator readout on
`CanonicalCompletedC3GlobalGreenOperatorCarrier`.

This is not an accident at one point.  The radial block vanishes along the
whole real collision direction.  The raw Wronskian is reconstructed there by
the retained Green-provenance, off-diagonal, readout-residual, and head--tail
completion channels.  Those channels occur in the six-channel scalar ledger,
but not in the candidate global operator carrier, whose first block contains
only the radial Green channel.

At the center the precise mismatch is

\[
 \langle X_{\mathrm{global}}(0),J_{\mathrm{global}}
 X_{\mathrm{global}}^{\mathrm{ref}}(0)\rangle
 =-|A(0)|^2W_{\mathrm{raw}}(0,0).
\]

Thus the existing global carrier does not implement the complete central
cancellation by itself.

## 3. First real collision variation

After the exact normalization already used by the central ledger, let

\[
 B_{\mathrm{global}}(t)=
 \frac{\langle X_{\mathrm{global}}(0),J_{\mathrm{global}}
 X_{\mathrm{global}}^{\mathrm{ref}}(t)\rangle}
 {N(t)}.
\]

Lean proves

\[
 B_{\mathrm{global}}'(0)
 =c_{\mathrm{replacement},1}
 =c_{\xi,1}-c_{C3,1}.
\]

This derivative is the natural operatorial form supplied by the current
global carrier.  It is a complex symplectic variation; no positivity or Gram
interpretation is used.

Adding the normalized raw boundary-symplectic branch gives the complete form

\[
 B_{\mathrm{total}}(t)=B_{\mathrm{raw}}(t)+B_{\mathrm{global}}(t).
\]

The central value and first variation are

\[
 B_{\mathrm{total}}(0)=0,
 \qquad
 B_{\mathrm{total}}'(0)=h_0.
\]

Equivalently,

\[
 h_0=c_{\mathrm{raw},1}
       +(c_{\xi,1}-c_{C3,1}).
\]

This reuses the existing central ledger derivative and channel derivative
theorems; it does not invoke theta.

## 4. First missing equality

For the current global carrier alone to have first variation `h0`, it would
be necessary and sufficient that

\[
 c_{\mathrm{raw},1}=0.
\]

Lean records exactly this equivalence in
`deriv_globalOperatorRealBranch_eq_h0_iff_rawVariation_zero`; it does not
assume or hide that equality.

Structurally, the missing operator block is the retained raw structural
difference

\[
 |A|^2\bigl(W_{\mathrm{raw}}-K_{\mathrm{radial}}\bigr).
\]

At the central real collision `K_radial` is zero, so this missing block is
exactly the raw term which cancels the archimedean/chart form.  Constructing
an operator carrier for that structural block would be genuinely new work;
none was introduced in this audit.

## 5. Clock quotient comparison

No positive tangent metric emerged on the existing global carrier.  The
operator appearing naturally is the symplectic complex structure, whereas
`Qport` and `Q3` are orthogonal projections acting on the native C3 port and
finite-prefix carriers.  There is currently no proved map carrying the full
raw structural symplectic variation into either clock-quotient carrier.

Therefore a comparison with `Qport` or `Q3` would presently identify forms
on different carriers and would be circular.  The established conclusion is
the narrower structural one:

- completion plus the complete raw ledger cancel the central flux;
- the state remains nonzero;
- the first variation of the complete normalized symplectic form is `h0`;
- the clock quotient may still remove a gauge direction from a later energy,
  but it does not remove or repair the central Wronskian;
- before testing that gauge interpretation, the raw structural channels need
  a common operatorial realization with the global carrier.
