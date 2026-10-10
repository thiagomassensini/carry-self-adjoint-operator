"""Require every public canary declaration in both audit and global registry."""
import json
import re
from pathlib import Path

root = Path(__file__).resolve().parents[1]
source = (root / 'CarrySelfAdjointOperator/MaterialChiralCoordinateCanary.lean').read_text()
declarations = re.findall(r'^(def|theorem)\s+(\w+)', source, re.M)
prefix = 'CarrySelfAdjointOperator.MaterialChiralCanary.'
names = [prefix + name for kind, name in declarations]
audit = (root / 'CarrySelfAdjointOperator/MaterialChiralCoordinateCanaryAudit.lean').read_text()
assert re.findall(r'^#print axioms (\S+)', audit, re.M) == names
assert re.findall(r'^#assert_material_chiral_canary_axioms (\S+)', audit, re.M) == names
registry = json.loads((root / 'audit/theorem-registry.json').read_text())
assert [entry['qualified'] for entry in registry['theorems']
        if entry['qualified'].startswith(prefix)] == names
assert len(names) == len(set(names))
print(f'material chiral registry passed: {len(names)} declarations, '
      f'{sum(kind == "theorem" for kind, name in declarations)} theorems')
