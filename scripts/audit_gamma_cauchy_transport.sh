#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
log_dir="${1:-.lake/gamma-cauchy-transport-audit}"
mkdir -p "$log_dir"
date -u +%Y-%m-%dT%H:%M:%SZ > "$log_dir/started-at.log"

lake env lean --version > "$log_dir/toolchain.log"
lake --version >> "$log_dir/toolchain.log"
git rev-parse HEAD > "$log_dir/base-commit.log"
git status --short --branch > "$log_dir/worktree-status.log"
python3 scripts/check_gamma_cauchy_transport_registry.py > "$log_dir/inventory.log"
git diff --check > "$log_dir/diff-check.log" 2>&1
git diff --cached --check >> "$log_dir/diff-check.log" 2>&1

mapfile -t modules < <(python3 -c 'import json; print("\n".join(m["module"] for m in json.load(open("audit/gamma-cauchy-transport-registry.json"))["modules"]))')
for module in "${modules[@]}"; do
  printf 'Checking %s\n' "$module"
  lake build --wfail "CarrySelfAdjointOperator.${module}Audit" > "$log_dir/${module}-build.log" 2>&1
  lake env lean "CarrySelfAdjointOperator/${module}Audit.lean" > "$log_dir/${module}-kernel.log" 2>&1
done

sha256sum CarrySelfAdjointOperator/NativeGamma*.lean audit/gamma-cauchy-transport-registry.json \
  scripts/check_gamma_cauchy_transport_registry.py scripts/audit_gamma_cauchy_transport.sh \
  > "$log_dir/source-sha256.log"
bash scripts/static_audit.sh > "$log_dir/static-audit.log" 2>&1
lake build --wfail > "$log_dir/root-build.log" 2>&1
bash scripts/audit.sh > "$log_dir/integration-audit.log" 2>&1
date -u +%Y-%m-%dT%H:%M:%SZ > "$log_dir/finished-at.log"
printf 'Gamma/material transport audit passed\n'
