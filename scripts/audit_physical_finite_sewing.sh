#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
sewing_log_dir="${1:-.lake/physical-finite-sewing-audit}"
mkdir -p "$sewing_log_dir"

sewing_modules=(
  NativePhysicalEndpointEncoder
  NativePhysicalFiniteSewing
  NativePhysicalMaterialProducer
  NativePhysicalTwoPortChart
  NativePhysicalEndpointCompletion
  NativePhysicalTfvdSecondPort
  NativePhysicalMixedProbes
  NativePhysicalLaguerreObservability
  NativePhysicalCameraCrossings
  NativePhysicalValveExtension
  NativePhysicalObservableCapstone
)

lake env lean --version > "$sewing_log_dir/toolchain.log"
lake --version >> "$sewing_log_dir/toolchain.log"
git rev-parse HEAD > "$sewing_log_dir/base-commit.log"
git status --short --branch > "$sewing_log_dir/worktree-status.log"
python3 scripts/check_physical_sewing_registry.py > "$sewing_log_dir/inventory.log"

for sewing_module in "${sewing_modules[@]}"; do
  printf 'Checking %s\n' "$sewing_module"
  lake build --wfail "CarrySelfAdjointOperator.${sewing_module}Audit" \
    > "$sewing_log_dir/${sewing_module}-build.log" 2>&1
  lake env lean "CarrySelfAdjointOperator/${sewing_module}Audit.lean" \
    > "$sewing_log_dir/${sewing_module}-kernel.log" 2>&1
done

bash scripts/static_audit.sh > "$sewing_log_dir/static-audit.log" 2>&1
git diff --check > "$sewing_log_dir/diff-check.log" 2>&1
lake build --wfail > "$sewing_log_dir/root-build.log" 2>&1
bash scripts/audit.sh > "$sewing_log_dir/integration-audit.log" 2>&1
printf 'Physical finite sewing audit passed\n'
