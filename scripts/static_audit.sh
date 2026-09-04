#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

trust_escape_pattern='(^|[^A-Za-z])(sorry|admit|axiom|unsafe)([^A-Za-z]|$)'
if command -v rg >/dev/null 2>&1; then
  trust_escape_scan=(rg -n --glob '*.lean')
else
  trust_escape_scan=(grep -RInE --include='*.lean')
fi

if "${trust_escape_scan[@]}" "$trust_escape_pattern" \
    CarrySelfAdjointOperator CarrySelfAdjointOperator.lean; then
  echo "static audit failed: local Lean trust escape found" >&2
  exit 1
fi

python3 -m json.tool audit/theorem-registry.json >/dev/null
python3 -m json.tool audit/br2-theorem-registry.json >/dev/null
bash -n scripts/audit.sh scripts/static_audit.sh

echo "static audit passed"
