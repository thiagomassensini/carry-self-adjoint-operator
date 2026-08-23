#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

bash scripts/static_audit.sh

# Fail first on the exact canonical LDL prefix proof.
lake build --wfail CarrySelfAdjointOperator.CanonicalLDLLowerInvPrefix
lake build --wfail CarrySelfAdjointOperator.CanonicalLDLPrefixReduction
lake build --wfail CarrySelfAdjointOperator.CanonicalProjectiveJacobiTower
lake build --wfail CarrySelfAdjointOperator.LDLCompatibilityAudit

# Keep the existing focused audits before rebuilding the full import surface.
lake build --wfail CarrySelfAdjointOperator.JacobiOrderPolynomial
lake build --wfail CarrySelfAdjointOperator.ExactProjectiveMatrixTower

# Surface the exact existing objects participating in the remaining scalar
# boundary trace before attempting any new composition theorem.
lake build --wfail CarrySelfAdjointOperator.CompletedBoundaryTraceTheoremSurface

lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
lake build --wfail CarrySelfAdjointOperator.BR2Audit
lake build --wfail CarrySelfAdjointOperator.OrderAudit

echo "kernel audit passed"
