#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

bash scripts/static_audit.sh

# Independent native incidence ports and literal-input source obstructions.
lake build --wfail CarrySelfAdjointOperator.NativeIncidenceCauchyPortsAudit
lake env lean CarrySelfAdjointOperator/NativeIncidenceCauchyPortsAudit.lean
lake build --wfail CarrySelfAdjointOperator.NativeIncidenceSourceProvenanceAudit
lake env lean CarrySelfAdjointOperator/NativeIncidenceSourceProvenanceAudit.lean

# First material edge, completed chiral state and full signed channels.
lake build --wfail CarrySelfAdjointOperator.FirstEdgeChiralStateComparisonAudit
lake env lean CarrySelfAdjointOperator/FirstEdgeChiralStateComparisonAudit.lean

# Relational log-gap connection, explicit seeded transport and signed defects.
lake build --wfail CarrySelfAdjointOperator.LogGapConnectionAudit
lake env lean CarrySelfAdjointOperator/LogGapConnectionAudit.lean

# Material-to-chiral coordinate canaries and full public axiom guard.
lake build --wfail CarrySelfAdjointOperator.MaterialChiralCoordinateCanaryAudit
lake env lean CarrySelfAdjointOperator/MaterialChiralCoordinateCanaryAudit.lean

# Material all-order vector transport and exact public axiom surface.
lake build --wfail CarrySelfAdjointOperator.FiniteMultibaseMaterialJetTransportAudit
lake env lean CarrySelfAdjointOperator/FiniteMultibaseMaterialJetTransportAudit.lean

# Check the observable quotient and native C3 clock/readout graph.
lake build --wfail CarrySelfAdjointOperator.ObservableJetAudit

# Check the discrete-projective capstone before the larger spectral surface.
lake build --wfail CarrySelfAdjointOperator.DiscreteProjectiveReconstructionAudit

# Check native incidence transport into projective-valve finite spans.
lake build --wfail CarrySelfAdjointOperator.ProjectiveValveNativeIncidenceAudit

# Check the moment obligations, derived carry energy and the two C3 obstructions.
lake build --wfail CarrySelfAdjointOperator.ProjectiveValveMomentFrontierAudit

# Check the constructed kernels and the exact native metric calibration.
lake build --wfail CarrySelfAdjointOperator.KernelConstructionAudit

# Check source-first local Hadamard jets, pole removal and camera universality.
lake build --wfail CarrySelfAdjointOperator.LocalHadamardMomentBridgeAudit
lake env lean CarrySelfAdjointOperator/LocalHadamardMomentBridgeAudit.lean

# Check formal logarithmic differentiation of the locally deflated completed jet.
lake build --wfail CarrySelfAdjointOperator.LocalHadamardFormalSeriesBridgeAudit
lake env lean CarrySelfAdjointOperator/LocalHadamardFormalSeriesBridgeAudit.lean

# Check analytic removal of the simple zero of completed F.
lake build --wfail CarrySelfAdjointOperator.LocalHadamardAnalyticDeflationAudit
lake env lean CarrySelfAdjointOperator/LocalHadamardAnalyticDeflationAudit.lean

# Check exact camera-to-moment universality before the operator audits.
lake build --wfail CarrySelfAdjointOperator.CompletedNativeCameraUniversalityAudit

# Check the positive Jacobi point-spectrum converse and its trust footprint.
lake build --wfail CarrySelfAdjointOperator.CompletedNativeJacobiPointSpectrumConverseAudit

# Cover the scalar boundary trace checked by the focused CI workflows.
lake build --wfail CarrySelfAdjointOperator.BoundaryTraceAudit

# Fail fast on the new ORDER layer before rebuilding the full import surface.
lake build --wfail CarrySelfAdjointOperator.JacobiOrderPolynomial
lake build --wfail CarrySelfAdjointOperator.ExactProjectiveMatrixTower
lake build --wfail CarrySelfAdjointOperator.CanonicalProjectiveJacobiTower

lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
lake build --wfail CarrySelfAdjointOperator.BR2Audit
lake build --wfail CarrySelfAdjointOperator.OrderAudit

lake build --wfail CarrySelfAdjointOperator.RecoveredC2GreenAudit
lake env lean CarrySelfAdjointOperator/RecoveredC2GreenAudit.lean

echo "kernel audit passed"
