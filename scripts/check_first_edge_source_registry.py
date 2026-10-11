"""Require complete registry and axiom audit coverage of the connection modules."""
import json
import re
from pathlib import Path

root = Path(__file__).resolve().parents[1]
modules = ['FirstEdgeChiralStateComparison']
declarations = []
for module in modules:
    source = (root / 'CarrySelfAdjointOperator' / (module + '.lean')).read_text()
    declarations += re.findall(r'^(def|theorem)\s+(\w+)', source, re.M)
prefix = 'CarrySelfAdjointOperator.FirstEdgeSewing.'
names = [prefix + name for kind, name in declarations]
audit = (root / 'CarrySelfAdjointOperator/FirstEdgeChiralStateComparisonAudit.lean').read_text()
assert re.findall(r'^#print axioms (\S+)', audit, re.M) == names
assert re.findall(r'^#assert_first_edge_source_axioms (\S+)', audit, re.M) == names
registry = json.loads((root / 'audit/theorem-registry.json').read_text())
assert [entry['qualified'] for entry in registry['theorems']
        if entry['qualified'].startswith(prefix)] == names
assert len(names) == len(set(names))
print(f'first-edge source registry passed: {len(names)} declarations, '
      f'{sum(kind == "theorem" for kind, name in declarations)} theorems')
