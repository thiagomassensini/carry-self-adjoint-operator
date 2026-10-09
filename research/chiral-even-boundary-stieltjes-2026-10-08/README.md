# Validation record — even raw boundary / Stieltjes minimal gate

Initial main: `3b6243691e5da87be25e5909b1ebfa33aa4217fa`.

- `new-modules.log`: `lake build --wfail` on all new modules and audits.
- `source-capstones.log`: direct `lake env lean` on the source/gate audit;
  prints raw split/phase/iff footprints and enforces dependency firewalls.
- `capstones.log`: direct `lake env lean` on the old-height handoff audit.
- `root-build.tail.log`, `root-audit.tail.log`: successful build endings.
- `static-audit.log`: successful static audit.
- `kernel-audit.tail.log`: complete script ending in `kernel audit passed`.
- Compressed `*.full.log.gz`: full authoritative output for root build,
  root Audit and the complete kernel-audit script, preserved alongside tails.
- `diff-check.log`: empty successful `git diff --check` output.
- `preserved-user-files.sha256`: unchanged user untracked Lean files.

Every validation exited zero. The universal boundary strict sign remains OPEN.
These logs certify the algebraic equivalence and conditional consumer, not that sign.
GitHub Actions is an independent publication/CI status, not substituted for the
successful direct Lean/kernel runs here.

Plain-text logs have trailing whitespace removed for `git diff --check`.
Compressed full logs preserve the exact original command output, including
`new-modules.full.log.gz`. No Lean source or theorem was changed by this
log-format normalization.
