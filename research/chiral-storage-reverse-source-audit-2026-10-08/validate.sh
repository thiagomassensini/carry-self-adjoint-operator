#!/usr/bin/env bash
set -euo pipefail
cd /home/thlinux/carry-self-adjoint-operator
export PATH="$HOME/.elan/bin:$PATH"
report_dir=research/chiral-storage-reverse-source-audit-2026-10-08
mkdir -p "$report_dir"
summary="$report_dir/validation-summary.txt"
printf 'Initial main: d0671e8127b93a178405aae3b4b7cf031d9a437d\nRemote validation host: llm\n' > "$summary"
run_step() {
  local label="$1"
  shift
  local log_path="/tmp/chiral-reverse-${label}.log"
  local status_code=0
  "$@" > "$log_path" 2>&1 || status_code=$?
  printf '%s: exit %s; log %s\n' "$label" "$status_code" "$log_path" | tee -a "$summary"
  if ((status_code != 0)); then tail -60 "$log_path"; return "$status_code"; fi
}
run_step new-builds lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnBoundaryCoefficientProvenance CarrySelfAdjointOperator.CompletedNativeChiralReturnBoundaryCoefficientProvenanceAudit
run_step coefficient-kernel lake env lean CarrySelfAdjointOperator/CompletedNativeChiralReturnBoundaryCoefficientProvenanceAudit.lean
cp /tmp/chiral-reverse-coefficient-kernel.log "$report_dir/coefficient-axioms-source-closure-and-open-signature.log"
run_step full-build lake build --wfail CarrySelfAdjointOperator
run_step umbrella-audit-build lake build --wfail CarrySelfAdjointOperator.Audit
run_step static-audit bash scripts/static_audit.sh
run_step kernel-audit bash scripts/audit.sh
run_step whitespace git diff --check
if rg -n '(^|[^A-Za-z])(sorry|admit|axiom|unsafe)([^A-Za-z]|$)|placeholder' CarrySelfAdjointOperator/CompletedNativeChiralReturnBoundaryCoefficientProvenance.lean CarrySelfAdjointOperator/CompletedNativeChiralReturnBoundaryCoefficientProvenanceAudit.lean > /tmp/chiral-reverse-placeholder.log; then
 printf 'placeholder scan: FAILED\n' | tee -a "$summary"
 exit 1
fi
printf 'placeholder scan: clean\nAllowed axioms: propext, Classical.choice, Quot.sound or subset\nSource closure: canonical moments, HP/Stieltjes, Hankel, Jacobi/height, Herglotz, BR2 rejected\nOpen boundary coercivity signature: type-checked Prop only, not a proof\nAll-order positivity: not claimed\n' | tee -a "$summary"
