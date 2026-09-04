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
# projections of one cutoff-one C3 TFVD/Green state.
lake build --wfail CarrySelfAdjointOperator.CompletedC3SameStructuredBoundaryState

# Compile the target-specific valve naturality bridge.  This identifies the
# weighted native TFVD bracket with the additive valve after the carry
# amplitude gauge, promotes the concrete Cp ordinary/log-jet split to the
# original depth-series curvature space, transports it exactly into the
# projective depth coordinate, and turns the additive split into a product of
# normalized masses.
lake build --wfail CarrySelfAdjointOperator.CompletedC3ValveNaturality

# Assemble the one-state naturality capstone from ledger boundary minus
# provenance, intrinsic C3 Green form, faithful six-camera source, Gamma state,
# and the completed scalar boundary pair (-F',F).
lake build --wfail CarrySelfAdjointOperator.CompletedC3ValveGreenNaturality

lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
lake build --wfail CarrySelfAdjointOperator.BR2Audit
lake build --wfail CarrySelfAdjointOperator.OrderAudit

echo "kernel audit passed"
