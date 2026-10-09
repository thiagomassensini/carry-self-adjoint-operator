# Surgical signed-jet transport validation

Initial main: `77c07339da3051000f1848a8612439c73322a359`.

Each `*.full.log.gz` preserves the complete original command output;
`*.tail.log` is its final 70 lines with trailing whitespace removed.
The logs cover both new targets with `--wfail`, direct Lean capstone checking,
root build, root Audit, static audit, the complete kernel script and diff checking.
Every command exited zero. `preserved-user-files.sha256` records the same two
user untracked files, not staged or edited.

The logs certify the signed finite synthesis and its exact boundary limit.
They do not certify dominance, PSD, strictness or an unconditional height result.
GitHub CI status is separate from these completed direct Lean/kernel runs.
