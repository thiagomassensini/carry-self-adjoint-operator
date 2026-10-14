# External native negative-channel certificates

See [the complete derivation and scope](../../docs/native-negative-channel-control.md).

- `certificate-512.json`: fresh Arb theta integration, 512 bits, 12 modes, spatial cutoff 128, degree 28.
- `certificate-768.json`: stronger run, 768 bits, 16 modes, spatial cutoff 256, degree 32.
- `audit.json`: source hashes, interval LDL replay, stronger-run overlap, direct theta source checks, and exact rational constants.

These are external certificates. No result or enclosure is imported as a Lean premise. The analytic calculus argument is documented and is not mechanically checked. The Lean module proves the general leakage estimates and conditional sign criteria.
