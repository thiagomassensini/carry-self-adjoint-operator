"""Check the complete public surface, source trust guard and preserved baseline."""
from pathlib import Path
import json,re,subprocess

p=Path(__file__).resolve().parent;r=p.parents[1]
modules=['NativeMaterialCameraBoundary','NativeMaterialBoundarySourceTransport','NativeMaterialBoundaryRegressions']
prefix='CarrySelfAdjointOperator.MaterialBoundarySewing.'

def lean_code(s):
    out=[];i=0;depth=0
    while i<len(s):
        if depth:
            if s.startswith('/-',i):depth+=1;i+=2
            elif s.startswith('-/',i):depth-=1;i+=2
            else:
                if s[i]=='\n':out.append('\n')
                i+=1
        elif s.startswith('/-',i):depth=1;i+=2
        elif s.startswith('--',i):
            j=s.find('\n',i);i=len(s) if j<0 else j
        else:out.append(s[i]);i+=1
    assert depth==0
    return ''.join(out)

rows=[]
for module in modules:
    code=lean_code((r/'CarrySelfAdjointOperator'/(module+'.lean')).read_text())
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',code),module
    assert re.findall(r'^namespace (\S+)',code,re.M)==[prefix.rstrip('.')]
    rows.append({'module':module,'declarations':[{'kind':kind,'qualified':prefix+name}
        for kind,name in re.findall(r'^(def|theorem) (\w+)',code,re.M)]})
names=[d['qualified'] for row in rows for d in row['declarations']]
assert len(names)==len(set(names))
registry=json.loads((r/'audit/material-boundary-sewing-registry.json').read_text())
assert registry=={'modules':rows,'public_roots':len(names)}
full=json.loads((r/'audit/theorem-registry.json').read_text())
assert [e['qualified'] for e in full['theorems'] if e['qualified'].startswith(prefix)]==names
audit=(r/'CarrySelfAdjointOperator/NativeMaterialBoundarySewingAudit.lean').read_text()
assert re.findall(r'^#print axioms (\S+)',audit,re.M)==names
guard=audit.split('#audit_physical_sewing\n')[1].split()
assert guard==names
assert 'import CarrySelfAdjointOperator.NativeMaterialBoundaryRegressions\n' in (r/'CarrySelfAdjointOperator.lean').read_text()
assert 'import CarrySelfAdjointOperator.NativeMaterialBoundarySewingAudit\n' in (r/'CarrySelfAdjointOperator/Audit.lean').read_text()

# The historical shell scanner counts the words 'admit'/'axiom' in three
# pre-existing comments. Compare that baseline without changing old proofs.
pattern=r'(^|[^A-Za-z])(sorry|admit|axiom|unsafe)([^A-Za-z]|$)'
base='045369f6dedcb2e75e9aefed1d12c9f73b9a2532'
def matches(ref):
    cmd=['git','grep','-n','-E',pattern]+([ref] if ref else [])+['--','CarrySelfAdjointOperator/*.lean','CarrySelfAdjointOperator.lean']
    ret=subprocess.run(cmd,cwd=r,capture_output=True,text=True)
    assert ret.returncode in [0,1]
    return ret.stdout.replace(base+':','')
baseline=matches(base);current=matches(None)
assert current==baseline,(baseline,current)
print(f'PASS: {len(names)} public roots, type/body audit registration, no new trust escapes')
print(f'PASS: historical raw scanner baseline unchanged ({len(baseline.splitlines())} comment matches)')
