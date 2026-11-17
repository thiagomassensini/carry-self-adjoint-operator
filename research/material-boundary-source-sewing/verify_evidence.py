from pathlib import Path
import gzip,hashlib,json,re
p=Path(__file__).resolve().parent;r=p.parents[1];e=p/'evidence'
m=json.loads((e/'VALIDATION.json').read_text())
for group,base in [('source_sha256',r),('evidence_sha256',e)]:
    for name,digest in m[group].items():
        assert hashlib.sha256((base/name).read_bytes()).hexdigest()==digest,name
assert len(m['commands'])==20 and all(row['exit_code']==0 for row in m['commands'])
audit=gzip.decompress((e/'research-kernel.log.gz').read_bytes()).decode()
registry=json.loads((r/'audit/material-boundary-sewing-registry.json').read_text())
names=[d['qualified'] for row in registry['modules'] for d in row['declarations']]
assert registry['public_roots']==m['public_roots']==len(names)==43
for name in names:assert name in audit,name
assert 'Physical sewing public roots: 43;' in audit
allowed={'propext','Classical.choice','Quot.sound'}
for name in ['research-kernel','inventory-native','inventory-green','inventory-geometry','inventory-operator']:
    log=gzip.decompress((e/(name+'.log.gz')).read_bytes()).decode()
    for axioms in re.findall(r'depends on axioms: \[([^\]]*)\]',log):
        assert {x.strip() for x in axioms.split(',') if x.strip()}<=allowed,(name,axioms)
print('PASS: all source/data/log hashes; 20 successful commands; 43 audited roots; standard axioms only')
