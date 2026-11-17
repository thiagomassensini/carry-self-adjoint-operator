"""Protect the original objects, effective dependencies and user work."""
from pathlib import Path
import hashlib,json,subprocess
p=Path(__file__).resolve().parent;r=p.parents[1]
d=json.loads((p/'evidence/provenance.json').read_text())
def git(path,*args):return subprocess.check_output(['git','-C',str(path),*args],text=True).strip()
for name,digest in d['protected_hashes'].items():
    assert hashlib.sha256((r/name).read_bytes()).hexdigest()==digest,name
for key in ['native','green','geometry']:
    row=d[key];path=Path(row['path'])
    assert git(path,'rev-parse','HEAD')==row['head'],key
    assert git(path,'status','--porcelain')==row['status'],key
for name,row in d['effective_packages'].items():
    assert git(Path(row['path']),'rev-parse','HEAD')==row['head'],name
allowed={'CarrySelfAdjointOperator.lean','CarrySelfAdjointOperator/Audit.lean',
 'CarrySelfAdjointOperator/NativeMaterialCameraBoundary.lean',
 'CarrySelfAdjointOperator/NativeMaterialBoundarySourceTransport.lean',
 'CarrySelfAdjointOperator/NativeMaterialBoundaryRegressions.lean',
 'CarrySelfAdjointOperator/NativeMaterialBoundarySewingAudit.lean',
 'audit/theorem-registry.json','audit/material-boundary-sewing-registry.json'}
changed=git(r,'diff','--name-only',d['operator']['base'],'--').splitlines()
assert all(n in allowed or n.startswith('research/material-boundary-source-sewing/') for n in changed),changed
assert git(r,'merge-base',d['operator']['base'],'HEAD')==d['operator']['base']
print('PASS: original mathematical objects, pins, dependencies and user files preserved')
