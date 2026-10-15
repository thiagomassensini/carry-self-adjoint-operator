# Divided vector response — 2026-10-15

Base: `e2ea3d26115e4e912d4352061f21ba567fae3496` in carry-self-adjoint-operator.

The response is `dslope sourceVector a z` in the existing enriched completed trace carrier. It is built from the original four normalized structural sectors and has a fixed linear readout. Its native scalar kernel, central value, source-defined prefixes and all-order coefficient/readout identities are proved without a positivity hypothesis.

This is a vector readout realization. It is not a positive Gram realization or the full infinite causal-interior lift. The moving-diagonal prefix convergence, a quantitative convergence rate and the all-order positivity gate are not claimed.

See `docs/native-completed-divided-vector-response.md`, the four matching Lean modules including the public audit, and `verification.json`. Dependency pins, metrics and amplitudes remain unchanged.
