# Finite diagnostic of the arbitrary-order source Schur formula

`probe.json` replays the published 1024-bit source intervals from
`research/native-kernel-series-2026-10-14/certificate-1024.json`.
It is finite external evidence, not fresh quadrature or an all-order sign proof.

The ten cases compare the exact source recurrence remainder, the Schur pivot,
the energy of its critical direction and an LDL factorization. The old odd
fourth pivot agrees with the eight-source certificate.

The all-order **identity and criterion**, and the **prefix-only countermodel**,
are separately kernel-checked in `NativeSourceAllOrderSchur.lean` and
`NativeMomentPrefixNoBootstrap.lean`. The altered countermodel is not the
native source and does not retain its global recurrence/theta representation.

See `docs/native-source-all-order-schur.md` for the remaining explicit source
inequality. Arbitrary-order native positivity remains open.
