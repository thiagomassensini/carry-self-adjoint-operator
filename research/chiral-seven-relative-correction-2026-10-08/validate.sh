#!/usr/bin/env bash
set -euo pipefail
cd /home/thlinux/carry-self-adjoint-operator
export PATH="$HOME/.elan/bin:$PATH"
report_dir=research/chiral-seven-relative-correction-2026-10-08
mkdir -p "$report_dir"
summary="$report_dir/validation-summary.txt"
printf 'Initial main: 45cf224813a4a786832ae7f14d755860fc48452b\nRemote validation host: llm\n' > "$summary"
run_step() {
  local label="$1"
  shift
  local log_path="/tmp/chiral-relative-${label}.log"
  local status_code=0
  "$@" > "$log_path" 2>&1 || status_code=$?
  printf '%s: exit %s; log %s\n' "$label" "$status_code" "$log_path" | tee -a "$summary"
  if ((status_code != 0)); then tail -70 "$log_path"; return "$status_code"; fi
}
modules=(FiniteQuadraticRelativeControl CompletedNativeChiralReturnSevenRelativeControl CompletedNativeChiralReturnSevenRelativeSpectrum CompletedNativeChiralReturnSevenRelativeRadius)
targets=()
for name in "${modules[@]}"; do targets+=("CarrySelfAdjointOperator.$name" "CarrySelfAdjointOperator.${name}Audit"); done
run_step new-builds lake build --wfail "${targets[@]}"
for name in "${modules[@]}"; do
  run_step "${name}-kernel" lake env lean "CarrySelfAdjointOperator/${name}Audit.lean"
  cp "/tmp/chiral-relative-${name}-kernel.log" "$report_dir/${name}-axioms-and-source-closure.log"
done
run_step full-build lake build --wfail CarrySelfAdjointOperator
run_step umbrella-audit-build lake build --wfail CarrySelfAdjointOperator.Audit
run_step static-audit bash scripts/static_audit.sh
run_step kernel-audit bash scripts/audit.sh
run_step whitespace git diff --check
scan_paths=()
for name in "${modules[@]}"; do scan_paths+=("CarrySelfAdjointOperator/$name.lean" "CarrySelfAdjointOperator/${name}Audit.lean"); done
if rg -n '(^|[^A-Za-z])(sorry|admit|axiom|unsafe)([^A-Za-z]|$)|placeholder' "${scan_paths[@]}" > /tmp/chiral-relative-placeholder.log; then
  printf 'placeholder scan: FAILED\n' | tee -a "$summary"
  exit 1
fi
printf 'placeholder scan: clean\nCapstones: only propext, Classical.choice, Quot.sound or subset\nSource dependency closure: canonical moments, HP/Stieltjes, Hankel, Jacobi/height, Herglotz, BR2 rejected\n' | tee -a "$summary"
