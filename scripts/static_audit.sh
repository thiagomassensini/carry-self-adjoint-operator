#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

if ! python3 scripts/scan_lean_trust_escapes.py; then
  echo "static audit failed: local Lean trust escape found" >&2
  exit 1
fi

python3 -m json.tool audit/theorem-registry.json >/dev/null
python3 -m json.tool audit/br2-theorem-registry.json >/dev/null
python3 -m json.tool audit/order-theorem-registry.json >/dev/null
python3 scripts/check_material_camera_jet_registry.py
python3 scripts/check_material_chiral_canary_registry.py
python3 scripts/check_log_gap_connection_registry.py
python3 scripts/check_first_edge_source_registry.py
python3 scripts/check_native_cauchy_ports_registry.py
python3 scripts/check_cauchy_laguerre_isometry_registry.py
bash -n scripts/audit.sh scripts/static_audit.sh scripts/audit_changed_lean.sh

echo "static audit passed"
