from pathlib import Path
import os,subprocess,concurrent.futures,json,hashlib,time
root=Path(__file__).resolve().parent
python='/home/thlinux/miniforge3/bin/python'
env=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
tasks=[('return_metric_covariance', 'native_carry_defect_return_metric_covariance_limit_lab.py',['--cameras','2,3,4,5,6,7','--identity-cutoffs','8,16,32,64','--covariance-cutoffs','128,512,2048,8192','--times','0,1,2','--output',str(root/'return_metric_covariance.json')]),('pythagorean_green','native_carry_pythagorean_green_measure_lab.py',['--sizes','8,16,32,64,128','--output',str(root/'pythagorean_green.json')]),('discrete_valve','c2_green_discrete_valve_return_audit.py',['--maximum-cells','12'])]
def run(task):
 name,file,args=task;started=time.time()
 with (root/(name+'.stdout')).open('w') as out,(root/(name+'.stderr')).open('w') as err:
  r=subprocess.run([python,str(root/'source_labs'/file),*args],cwd=root/'source_labs',env=env,stdout=out,stderr=err,timeout=1200)
 return {'name':name,'exit_code':r.returncode,'elapsed_sec':time.time()-started}
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool: results=list(pool.map(run,tasks))
records=json.loads((root/'labs_source_manifest.json').read_text())
for record in records: record['original_unchanged']=hashlib.sha256(Path(record['original']).read_bytes()).hexdigest()==record['sha256']
summary={'tasks':results,'sources':records}
(root/'labs_execution_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'tasks':results,'all_originals_unchanged':all(r['original_unchanged'] for r in records)},indent=2))
