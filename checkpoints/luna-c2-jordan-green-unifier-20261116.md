# Luna — C2 / Jordan / Schur / Green unifier

## Scope

This follow-up composes the already-proved fixed-order transports from the C2
central-plus-legs readout, the original signed Jordan channels, the canonical
Schur pivot, and the theta-Green integral. It does not prove an all-order
sign. The integration branch is stacked on carry-self-adjoint-operator PR
#119, which itself depends on #118; it does not alter either existing PR
worktree.

## Main declaration

`CarrySelfAdjointOperator.nativeCriticalC2JordanGreenLimit` takes a sector
`b : Bool`, a Schur order `n`, and positive definiteness of the old
`n × n` source prefix. It proves together:

- the C2 readout at order `n+1` tends to `p_(s,n)/2`;
- the original signed Jordan channel energy, after its `c₀/4` scaling, tends
  to the native remainder;
- the remainder is `2*c₀*(p_(s,n)/2)`;
- the same remainder is exactly the complete theta-Green integral.

The index `n+1` is essential: the Schur critical vector extends the old
prefix to size `n+1`. All original factors are retained. The Jordan norms
retain their crossed channel contributions. The theorem is signed and has no
positivity conclusion.

The same module adds conditional sign corollaries from positivity of the
enlarged prefix: the even Euler integral is strictly positive, while the odd
Euler integral satisfies `-2*c₀*ρ² < I_odd`. The Green integral is positive
under the same enlarged-prefix condition because `c₀ > 0` and the Schur
complement is positive.

## Finite H6/K6 instantiation

The GoN follow-up branch based on PR #331 adds
`CanonicalNativeBoundaryTransfer.nativeCriticalGreenPositive_of_order_le_five`
and finite even/odd Euler consequences. It applies the existing H6/K6
restriction theorem at size `n+1`; since `n ≤ 5`, this size is at most six.
The dependency stays one-way: Geometry of Numbers imports the Carry theorem,
and Carry does not import Geometry of Numbers.

## Current validation

- Carry focal source and audit compiled with `-DwarningAsError=true` against
  the existing #118/#119 Lean environment.
- `bash research/canonical-native-boundary-transfer/compile_module.sh
  CanonicalBoundaryTransfer /home/thlinux/worktrees/luna-c2-euler-geometric-sign-20261116`
  passed for the GoN finite corollaries.
- The corresponding GoN `Audit` module passed and printed only
  `propext`, `Classical.choice`, and `Quot.sound` for the new roots.
- A clean `lake build --wfail
  CarrySelfAdjointOperator.NativeCriticalC2JordanGreenLimitAudit` is running
  in the Carry integration worktree; record its final result before
  publication.
- PR #331 is open and unmerged. Its H6/K6 finite certificate is an explicit
  dependency; it proves no order-uniform or all-order estimate.

## Remaining gap

The next unproved obligation is still a geometric source estimate that
controls the signed channel balance beyond the finite certified range. The
C2 limit and the Green identity identify the same scalar; neither estimates
the negative channel by the positive one. PR #124's additive return budget
remains a sufficient open premise, not a proved source inequality.
