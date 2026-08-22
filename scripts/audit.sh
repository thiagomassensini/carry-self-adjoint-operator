#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

bash scripts/static_audit.sh
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
lake build --wfail CarrySelfAdjointOperator.BR2Audit
lake build --wfail CarrySelfAdjointOperator.OrderAudit

echo "kernel audit passed"
