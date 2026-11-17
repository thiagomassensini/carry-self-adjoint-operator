"""Run the exact required checks; retain commands, exits, logs and hashes."""
from pathlib import Path
import gzip,hashlib,json,os,subprocess,time
p=Path(__file__).resolve().parent;r=p.parents[1];e=p/'evidence'
env=os.environ.copy();env['PATH']='/home/thlinux/.elan/bin:'+env.get('PATH','')
env['PYTHONDONTWRITEBYTECODE']='1'
rows=[]
def run(name,cmd,cwd=r):
    started=time.monotonic()
    with (e/(name+'.log')).open('w') as f:
        ret=subprocess.run(cmd,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT)
    rows.append(dict(name=name,command=cmd,cwd=str(cwd),exit_code=ret.returncode,seconds=time.monotonic()-started))
    (e/'commands.json').write_text(json.dumps(rows,indent=2)+'\n')
    if ret.returncode:
        print((e/(name+'.log')).read_text()[-12000:],flush=True)
        raise SystemExit(ret.returncode)
    print('PASS: '+name,flush=True)

run('provenance',['python3',str(p/'verify_provenance.py')])
run('registry',['python3',str(p/'check_registry.py')])
run('native-pr15-build',['lake','build','--wfail','NativeCarrySpectralWeyl.Finite.RelationalDivisibilityGram'],Path('/home/thlinux/native-carry-spectral-weyl'))
for name,path in [('native','native-carry-spectral-weyl'),('green','carry-self-adjoint-operator'),('geometry','geometry-of-numbers'),('operator','carry-self-adjoint-operator')]:
    run('inventory-'+name,['lake','env','lean',str(p/('inventory-'+name+'.lean'))],Path('/home/thlinux')/path)
run('research-build',['lake','build','--wfail','CarrySelfAdjointOperator.NativeMaterialCameraBoundary',
    'CarrySelfAdjointOperator.NativeMaterialBoundarySourceTransport',
    'CarrySelfAdjointOperator.NativeMaterialBoundaryRegressions',
    'CarrySelfAdjointOperator.NativeMaterialBoundarySewingAudit'])
run('research-kernel',['lake','env','lean','CarrySelfAdjointOperator/NativeMaterialBoundarySewingAudit.lean'])
for name in ['material_camera_jet','material_chiral_canary','log_gap_connection','first_edge_source','native_cauchy_ports','cauchy_laguerre_isometry']:
    run('prior-registry-'+name,['python3','scripts/check_'+name+'_registry.py'])
run('root-build',['lake','build','--wfail'])
run('root-audit-build',['lake','build','--wfail','CarrySelfAdjointOperator.Audit'])
run('root-audit-kernel',['lake','env','lean','CarrySelfAdjointOperator/Audit.lean'])
run('diff-check',['git','diff','--check'])
run('final-provenance',['python3',str(p/'verify_provenance.py')])

assert len(rows)==20 and all(row['exit_code']==0 for row in rows)
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
for f in sorted(e.glob('*.log')):
    f.with_suffix('.log.gz').write_bytes(gzip.compress(f.read_bytes(),mtime=0));f.unlink()
source_paths=[r/'CarrySelfAdjointOperator.lean',r/'CarrySelfAdjointOperator/Audit.lean',
    r/'audit/theorem-registry.json',r/'audit/material-boundary-sewing-registry.json']
source_paths+=sorted((r/'CarrySelfAdjointOperator').glob('NativeMaterial*.lean'))
source_paths+=[f for f in sorted(p.iterdir()) if f.is_file()]
manifest={'base':json.loads((e/'provenance.json').read_text())['operator']['base'],
    'head_at_validation':subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip(),
    'public_roots':43,'commands':rows,
    'source_sha256':{str(f.relative_to(r)):sha(f) for f in source_paths},
    'evidence_sha256':{f.name:sha(f) for f in sorted(e.iterdir()) if f.is_file() and f.name!='VALIDATION.json'},
    'historical_static_scanner':'raw script has three pre-existing comment false positives; unchanged baseline checked by registry.py',
    'status':'PASS: universal physical border identity and localized antipodal obstruction; full positivity bridge OPEN'}
(e/'VALIDATION.json').write_text(json.dumps(manifest,indent=2)+'\n')
subprocess.run(['python3',str(p/'verify_evidence.py')],cwd=r,env=env,check=True)
