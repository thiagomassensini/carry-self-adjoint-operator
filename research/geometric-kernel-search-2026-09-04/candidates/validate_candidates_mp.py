#!/usr/bin/env python3
import os
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[k]='1'
import concurrent.futures,json
from fractions import Fraction
from pathlib import Path
import mpmath as mp
import carry_candidates as cc
BASE=Path(__file__).resolve().parent.parent
def job(task):
 b,N,kind,source=task;mp.mp.dps=90;q=1/mp.sqrt(b)
 cc.inner=lambda x,y:mp.fsum(a*b for a,b in zip(x,y))
 if source=='delta1':u=[mp.mpf(0),mp.mpf(1)]+[mp.mpf(0)]*(N-2)
 else:u=[q**n for n in range(N)]
 t=cc.causal if kind=='analysis_gram' else cc.synthesis
 m=cc.moment_sequence(u,lambda v:t(t(v,q),q,True),12)
 c=[(v/m[0])/((m[1]/m[0])**k) for k,v in enumerate(m)]
 ref=json.loads((BASE/'reference/native_moments.json').read_text());h=list(map(mp.mpf,ref['h'][:13]));hc=[(v/h[0])/((h[1]/h[0])**k) for k,v in enumerate(h)]
 return {'base':b,'N':N,'family':kind,'source':source,'dps':90,'moments':[mp.nstr(v,80) for v in m],'scale_free_moments':[mp.nstr(v,80) for v in c], 'scale_free_relative_error':[mp.nstr(x/y-1,60) for x,y in zip(c,hc)]}
def exact_return(b,kmax):
 # q-weighted coefficients a_n for x_n=q^n a_n, with finite support after first V.
 r=Fraction(1,b)
 def V(a):
  n=len(a)+2
  def v(i):return a[i] if 0<=i<len(a) else Fraction(0)
  def c(i):return v(i)-2*v(i-1)+v(i-2) if i>=0 else Fraction(0)
  return [b*c(i)-2*c(i+1)+r*c(i+2) for i in range(n)]
 m=[Fraction(b,b-1),Fraction(b+1)]
 a=[Fraction(b+2),Fraction(-b)]
 for k in range(2,kmax+1):
  a=V(a);m.append(sum(x*r**i for i,x in enumerate(a)))
 assert m[2]==(b+1)*(b+4)
 return {'base':b,'family':'analysis_gram','source':'return_value','exact_moments':[str(x) for x in m],'exact_scale_free_moments':[str(x*m[0]**(k-1)/m[1]**k) for k,x in enumerate(m)]}
if __name__=='__main__':
 jobs=[(b,N,kind,src) for b,kind,src in [(3,'analysis_gram','return_value'),(5,'synthesis_gram','delta1'),(6,'synthesis_gram','delta1')] for N in (64,128,256)]
 with concurrent.futures.ProcessPoolExecutor(max_workers=3) as ex:rows=list(ex.map(job,jobs))
 out={'schema':'carry-geometric-candidates-mp-v1','results':rows,'exact_return_moments':[exact_return(b,12) for b in range(2,8)]}
 (BASE/'candidates/validation_mp.json').write_text(json.dumps(out,indent=2))
 print('written MP90 rows',len(rows),'exact rational rows',6,flush=True)
 for r in rows:
  if r['N']==256:print(r['base'],r['family'],r['source'],r['scale_free_moments'][2:5],flush=True)
