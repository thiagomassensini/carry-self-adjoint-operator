"""Check the new material transport surface against its public registry/audit."""
import json
import re
from pathlib import Path

root = Path(__file__).resolve().parents[1]
modules = [
    'FiniteMultibaseMaterialJetTower', 'FiniteMultibaseMaterialBracketTransport',
    'FiniteMaterialCameraGreenTransport', 'FiniteMaterialTfvdJetTransport',
    'RelationalMaterialClockAllOrder',
]
prefix = 'CarrySelfAdjointOperator.MaterialCameraJets.'
names = []
theorems = 0
for module in modules:
    text = (root / 'CarrySelfAdjointOperator' / (module + '.lean')).read_text()
    declarations = re.findall(r'^(?:@\[[^\n]*\]\s*)?(def|abbrev|theorem)\s+(\w+)', text, re.M)
    names.extend(prefix + name for kind, name in declarations)
    theorems += sum(kind == 'theorem' for kind, name in declarations)
audit = (root / 'CarrySelfAdjointOperator/FiniteMultibaseMaterialJetTransportAudit.lean').read_text()
assert re.findall(r'^#print axioms (\S+)', audit, re.M) == names
assert re.findall(r'^#assert_material_camera_jet_axioms (\S+)', audit, re.M) == names
registry = json.loads((root / 'audit/theorem-registry.json').read_text())
entries = [e['qualified'] for e in registry['theorems']]
assert [n for n in entries if n.startswith(prefix)] == names
assert len(names) == len(set(names))
print(f'material jet registry passed: {len(names)} declarations, {theorems} theorems')
