# Luna F — exact C2 tail in the original carrier

## Scope and base

Work was isolated in branch `codex/luna-f-exact-tail-2026-11-14`, based on
PR #116's reference commit
`9ac5f633b2f06ea95b036b0e4add6ee33dff21eb`. The original checkout and PR #116
were left untouched.

The proof uses the native C2 finite head and the omitted whole-center series
already present in `C2GeometryNativeSourceBridge.lean`. The cutoff `M` counts
included C2 cells; `k` remains the radial Cauchy node index; `n` remains the
Hankel order. No asymptotic replacement, Euler–Maclaurin formula, or alternate
zeta representation is introduced.

## Results proved

`CompletedNativeC2ExactTailTransport.lean` proves:

- Luna E's completed finite numerator is exactly the original completion
  dressing times `finiteBracketCharacteristic 2 M` at
  `operatorHeightParameter z`. The source Hermite–Biehler denominator remains
  the separate original carrier weight.
- On the genuine strip,
  `completedNativeOperatorCharacteristic z - c2FiniteChartHeightCharacteristic M z`
  equals `c2CompletionDressing z * T_M(s(z))`, where `T_M` is the exact series
  of omitted complete centers.
- The companion difference is exactly
  `-deriv (fun z => L(z) * T_M(s(z)))`. Its expanded form retains `L'`, `T_M'`,
  and `s'(z)=i`; the quotient derivative of `L=A/B₂` explicitly contains the
  completion-factor derivative and the original C2 camera-factor derivative.
- Both identities transport through the original finite Cauchy synthesis,
  with the unchanged `nativeSourceC2SourceWeight`, all radial nodes, and the
  existing `completedNativeRadialChiralCauchyState` vectors.

`CompletedNativeC2ExactTailConvergence.lean` proves:

- For each fixed `(n,k)` whose finite nodes lie in the strip, the value and
  companion tail operators have explicit finite row-sum bounds that tend to
  zero as `M → ∞`.
- This gives convergence uniformly over the closed unit ball of every input
  vector for both channels. It is operator-norm control for fixed `n,k`; no
  uniformity in `k` is used or asserted.
- The E2 tail error is at most an explicit sensitivity coefficient times
  `‖x‖²`, uniformly for every `x`. For fixed `(n,k)` that coefficient tends to
  zero with `M`.
- The diagonal cutoff `nativeSourceC2TailCutoff n k` is selected using budget
  `b_n(k)=1/(k+1)`. For each fixed `n`, the original radial nodes are
  eventually in the strip, so eventually in `k` the E2 error is at most
  `b_n(k)‖x‖²` for every input vector. The budget tends to zero.
- `nativeSourceC2ChosenCutoffSign_implies_legTailBounds` combines this proved
  tail half with only the still-open central-plus-legs sign estimate at that
  exact same diagonal cutoff. No compatibility between different cutoffs is
  assumed.

## Remaining hypotheses and limits

The central-plus-legs sign estimate remains an explicit hypothesis. Thus this
work does **not** prove unconditional positivity, Hankel positivity, or
`InfinitePositiveRealNativeZeros`; the latter must remain explicit in any final
consumer. The exact tail-decay half of `HasNativeSourceC2LegTailBounds` is no
longer an independent hypothesis.

The scalar tail limits use the repository's existing locally uniform
convergence of the finite bracket characteristic and its derivative, via
`finiteBracketCharacteristic_tendsto` and
`deriv_finiteBracketCharacteristic_tendsto`. The passage to the source
carrier is justified by its finite node count and the explicit norm of the
existing source-coordinate matrix. The radial-domain condition is only needed
eventually for fixed order; no claim uniform over all radial indices is made.

The pre-existing
`canonicalC2Geometry_completedPackagedNativeJet_eq_head_add_exactTail` also
records that the same exact head-plus-tail identity passes through every
native-line derivative order. The new companion proof uses the stronger
complex local-uniform derivative limit at each carrier node so the product
rule and `s'(z)=i` are visible in the original complex Cauchy channel.

No new axiom, `sorry`, or `admit` was added. The separate audit module prints
transitive axioms for the main bridge, convergence, diagonal-budget, and E4
interface theorems.

## Verification

- `lake build --wfail` for the three new Lean modules completed successfully
  (9,639 build jobs).
- `lake env lean -DwarningAsError=true` compiled each of the three modules.
- `scripts/audit_changed_lean.sh 9ac5f633b2f06ea95b036b0e4add6ee33dff21eb HEAD`
  passed. The axiom checker accepted all 15 reports; they contain only Lean's
  standard `propext`, `Classical.choice`, and `Quot.sound` axioms.
- `git diff --cached --check` passed before the commit.
