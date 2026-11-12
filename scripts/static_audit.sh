#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

# Scan executable Lean text, ignoring line and nested block comments.
# Preserve the existing trust-escape keyword detection in code and strings.
python3 - <<'PY'
from pathlib import Path
import re
import sys

trust_escape_pattern = re.compile(
    r'(^|[^A-Za-z])(sorry|admit|axiom|unsafe)([^A-Za-z]|$)'
)

def strip_lean_comments(source):
    output = []
    i = 0
    depth = 0
    line_comment = False
    in_string = False
    escaped = False

    while i < len(source):
        char = source[i]
        pair = source[i:i + 2]
        if line_comment:
            if char == '\n':
                line_comment = False
                output.append('\n')
            else:
                output.append(' ')
            i += 1
        elif depth:
            if pair == '/-':
                depth += 1
                output.extend('  ')
                i += 2
            elif pair == '-/':
                depth -= 1
                output.extend('  ')
                i += 2
            else:
                output.append('\n' if char == '\n' else ' ')
                i += 1
        elif in_string:
            # Keep scanning string contents, including interpolated Lean code.
            output.append(char)
            if escaped:
                escaped = False
            elif char == '\\':
                escaped = True
            elif char == '"':
                in_string = False
            i += 1
        elif pair == '--':
            line_comment = True
            output.extend('  ')
            i += 2
        elif pair == '/-':
            depth = 1
            output.extend('  ')
            i += 2
        elif char == '"':
            in_string = True
            output.append(char)
            i += 1
        else:
            output.append(char)
            i += 1

    return ''.join(output)

paths = [Path('CarrySelfAdjointOperator.lean'),
         *Path('CarrySelfAdjointOperator').rglob('*.lean')]
violations = []
for path in sorted(paths):
    code = strip_lean_comments(path.read_text(encoding='utf-8'))
    for number, line in enumerate(code.splitlines(), start=1):
        if trust_escape_pattern.search(line):
            violations.append(f'{path}:{number}:{line.strip()}')

if violations:
    print('static audit failed: Lean trust escape found in source', file=sys.stderr)
    print('\n'.join(violations), file=sys.stderr)
    raise SystemExit(1)
PY

python3 -m json.tool audit/theorem-registry.json >/dev/null
python3 -m json.tool audit/br2-theorem-registry.json >/dev/null
python3 -m json.tool audit/order-theorem-registry.json >/dev/null
python3 scripts/check_material_camera_jet_registry.py
python3 scripts/check_material_chiral_canary_registry.py
python3 scripts/check_log_gap_connection_registry.py
python3 scripts/check_first_edge_source_registry.py
python3 scripts/check_native_cauchy_ports_registry.py
python3 scripts/check_cauchy_laguerre_isometry_registry.py
bash -n scripts/audit.sh scripts/static_audit.sh

echo "static audit passed"
