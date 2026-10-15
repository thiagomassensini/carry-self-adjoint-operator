#!/usr/bin/env python3
"""Audit existing outward intervals; no new moment computation or positivity extension."""
import argparse
import hashlib
import json
from pathlib import Path
from flint import arb, ctx

parser = argparse.ArgumentParser()
parser.add_argument('--repo', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
ctx.prec = 1024
src = args.repo / 'research/theta-adaptive-prefix-2026-10-15/adaptive-budget-cert-1024.json'
data = json.loads(src.read_text())
assert data['status'] == 'EXTERNAL_ARB_FINITE_ADAPTIVE_SOURCE_MARGIN_CERTIFIED'
assert data['different_precision_replication_overlaps']

rows = []
for n, sector in [(2, 1), (3, 0)]:
    row = next(x for x in data['rows'] if x['n'] == n and x['sector'] == sector)
    central = arb(row['Q_coefficients_in_y_u_squared'][1])
    remainder = arb(row['R'])
    assert central < 0 and remainder > 0
    rows.append({
        'n': n,
        'sector': sector,
        'source_polynomial_u2_coefficient': str(central),
        'source_R': str(remainder),
        'central_coefficient_strictly_negative': True,
        'source_R_strictly_positive': True,
    })

result = {
    'status': 'AUDIT_OF_EXISTING_FINITE_INTERVALS_ONLY',
    'parent_certificate_sha256': hashlib.sha256(src.read_bytes()).hexdigest(),
    'parent_certificate': str(src.relative_to(args.repo)),
    'new_quadrature': False,
    'new_positivity_range': False,
    'Lean_premise': False,
    'rows': rows,
}
args.output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps([
    {key: value for key, value in row.items() if key in (
        'n', 'sector', 'central_coefficient_strictly_negative', 'source_R_strictly_positive'
    )}
    for row in rows
]))
