# Mixed return ray: actual native camera readout

The atlas note led to a source-level realization of the previously selected camera return ray. The new Lean module applies `(-6,-3,2,0,3,0)` to the six actual head-plus-tail characteristics, computes its factor `-4*d2*A3`, and proves the native modal energy coefficient `8/139`. Normalization and native completion recover the operator characteristic, all height derivatives, even coefficients and reciprocal formal mass.

The native positive response-kernel identification remains open. The scalar mass theorem is not an identification of moments of an independently constructed positive observable.

- [Source map](../../docs/atlas-mixed-return-native-readout.md): formulas, exact declarations, atlas correction and remaining equality.
- [verification.json](verification.json): ten declarations, standard transitive axioms, unchanged dependency pins and hashes.
- [note-sources.json](note-sources.json): original note hash and source snapshots; the original was preserved.
- `specific-build.log.gz`, `full-audit.log.gz`: successful local logs, the latter containing all 14 required Lake builds with `--wfail` and the static audit.

Reproduction from the recorded dependency pins:

```bash
lake build --wfail CarrySelfAdjointOperator.MixedReturnNativeReadout
bash scripts/audit.sh
```

No numerical fitting or new numerical experiments were needed for these algebraic and analytic transport proofs. GitHub CI was not monitored.
