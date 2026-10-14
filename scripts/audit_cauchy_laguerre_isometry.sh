#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
laguerre_log_dir="${1:-.lake/cauchy-laguerre-isometry-audit}"
mkdir -p "$laguerre_log_dir"
date -u +%Y-%m-%dT%H:%M:%SZ > "$laguerre_log_dir/started-at.log"
lake env lean --version > "$laguerre_log_dir/toolchain.log"
lake --version >> "$laguerre_log_dir/toolchain.log"
git rev-parse HEAD > "$laguerre_log_dir/base-commit.log"
git status --short --branch > "$laguerre_log_dir/worktree-status.log"
python3 scripts/check_cauchy_laguerre_isometry_registry.py > "$laguerre_log_dir/inventory.log"
python3 scripts/check_gamma_cauchy_transport_registry.py > "$laguerre_log_dir/preserved-inventory.log"
git diff --check > "$laguerre_log_dir/diff-check.log"
mapfile -t laguerre_modules < <(python3 -c 'import json; print("\n".join(m["module"] for m in json.load(open("audit/cauchy-laguerre-isometry-registry.json"))["modules"]))')
for laguerre_module in "${laguerre_modules[@]}"; do
  printf 'Checking %s\n' "$laguerre_module"
  lake build --wfail "CarrySelfAdjointOperator.${laguerre_module}Audit" > "$laguerre_log_dir/${laguerre_module}-build.log" 2>&1
  lake env lean -E warning "CarrySelfAdjointOperator/${laguerre_module}Audit.lean" > "$laguerre_log_dir/${laguerre_module}-kernel.log" 2>&1
done
sha256sum lake-manifest.json lean-toolchain CarrySelfAdjointOperator/NativeCauchyLaguerre*.lean \
  CarrySelfAdjointOperator/NativeCauchyHardyStep*.lean audit/cauchy-laguerre-isometry-registry.json \
  scripts/check_cauchy_laguerre_isometry_registry.py scripts/audit_cauchy_laguerre_isometry.sh \
  > "$laguerre_log_dir/source-sha256.log"
bash scripts/static_audit.sh > "$laguerre_log_dir/static-audit.log" 2>&1
lake build --wfail > "$laguerre_log_dir/root-build.log" 2>&1
bash scripts/audit.sh > "$laguerre_log_dir/integration-audit.log" 2>&1
date -u +%Y-%m-%dT%H:%M:%SZ > "$laguerre_log_dir/finished-at.log"
printf 'Physical Cauchy-Laguerre isometry audit passed\n'
