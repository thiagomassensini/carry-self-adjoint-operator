# External certificates: continuous native grid range

These are external Arb certificates, not Lean positivity proofs.

See `docs/native-kernel-series.md` for the analytic identification and
infinite-tail derivation. The coefficient majorant alone is kernel-checked
in `CompletedNativeLogCoefficientMajorant.lean`.

Fresh theta integrations at 768 and 1024 bits certify the unchanged native
source form for **every** `h` in `[0,H]`, including its boundary limit:

| N | H | Original grid |
|---:|---:|---:|
| 8 | 1/256 | all k >= 255 |
| 10 | 1/2048 | all k >= 2047 |
| 12 | 1/32768 | all k >= 32767 |

`audit.json` replays the bounds, compares the independent integrations, and
checks all mixed storage entries against the original quotient, amplitudes,
physical Cauchy metric and binomial chart at two nodes per dimension.

The auxiliary exact rational congruence is used only to verify positivity;
the original source and physical operator are never redefined by it.
General positivity for arbitrary N remains open.
