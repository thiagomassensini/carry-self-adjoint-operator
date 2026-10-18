from pathlib import Path
import subprocess,json,re
root=Path(__file__).resolve().parents[2]
evidence=Path(__file__).resolve().parent/'evidence'
run=subprocess.run(['bash','scripts/static_audit.sh'],cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
(evidence/'static-audit.log').write_text(run.stdout)
hits=[]
for line in run.stdout.splitlines():
    m=re.match(r'(CarrySelfAdjointOperator/[^:]+):(\d+):(.*)',line)
    if not m: continue
    path,num,content=m.groups()
    old=subprocess.check_output(['git','show','045369f6dedcb2e75e9aefed1d12c9f73b9a2532:'+path],cwd=root,text=True).splitlines()
    assert old[int(num)-1]==content,(path,num)
    assert re.search(r'/--|-/|axiom',content),content
    hits.append(dict(path=path,line=int(num),unchanged_from_base=True,text=content))
assert run.returncode==1 and len(hits)==3,run.stdout
assert {h['path'] for h in hits}=={'CarrySelfAdjointOperator/NativeSourceAllOrderSchur.lean','CarrySelfAdjointOperator/NativeMomentPrefixNoBootstrap.lean','CarrySelfAdjointOperator/CompletedNativeChiralReturnLeakageControl.lean'}
result=dict(scanner_exit_code=run.returncode,status='BASELINE COMMENT MATCHES ONLY; SCANNER DID NOT PASS',hits=hits)
(evidence/'static-baseline.json').write_text(json.dumps(result,indent=2)+'\n')
print(result['status'])
