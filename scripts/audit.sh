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

# Compile the experimental Green-inverse sewing criterion even before it is
# wired into the public aggregator.
lake build --wfail CarrySelfAdjointOperator.CompletedC3GreenInverseSewingProbe

# Compile the boundary-relation reformulation independently as well.  This
# makes the six-camera Gamma boundary Green form and the completed scalar
# Wronskian meet in one typed interface before any aggregator wiring.
lake build --wfail CarrySelfAdjointOperator.CompletedC3BoundaryRelationSewingBridge

# Compile the sharper same-structured-state bridge.  It proves that the
# Gamma six-camera source and the oriented scalar trace (-F',F) are both
# projections of one cutoff-one C3 TFVD/Green state, while retaining the
# existing no-go against treating the packing itself as a Green intertwiner.
lake build --wfail CarrySelfAdjointOperator.CompletedC3SameStructuredBoundaryState

lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
lake build --wfail CarrySelfAdjointOperator.BR2Audit
lake build --wfail CarrySelfAdjointOperator.OrderAudit

echo "kernel audit passed"
