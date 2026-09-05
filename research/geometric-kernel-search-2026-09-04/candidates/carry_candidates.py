#!/usr/bin/env python3
"""Geometry-fixed candidate moments. No native target, fitting, or zeta input.
All finite operator applications are explicit; N is a hard wall and gets varied.
"""
import os
for key in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
 os.environ[key]='1'
import argparse, concurrent.futures, json, math
from fractions import Fraction
from pathlib import Path


def inner(x,y): return math.fsum(a*b for a,b in zip(x,y))
def causal(v,q,adj=False):
 n=len(v);o=[0.0]*n
 if adj:
  for k in range(n):o[k]=v[k]/q-(2*v[k+1] if k+1<n else 0)+(q*v[k+2] if k+2<n else 0)
 else:
  for k in range(n):o[k]=v[k]/q-(2*v[k-1] if k else 0)+(q*v[k-2] if k>=2 else 0)
 return o

def synthesis(v,q,adj=False):
 # q(I-qU)^-2, inverse of the literal lower triangular A_N.
 a=[0.0]*len(v);b=[0.0]*len(v)
 if adj:
  for k in range(len(v)-1,-1,-1):a[k]=v[k]+(q*a[k+1] if k+1<len(v) else 0)
  for k in range(len(v)-1,-1,-1):b[k]=q*a[k]+(q*b[k+1] if k+1<len(v) else 0)
 else:
  for k in range(len(v)):a[k]=v[k]+(q*a[k-1] if k else 0)
  for k in range(len(v)):b[k]=q*a[k]+(q*b[k-1] if k else 0)
 return b

def green(v,q,adj=False):
 # G=q U(I-qU)^-2 = U A^-1; exact existing kernel r q^r.
 if adj:return synthesis(v[1:]+[0.0],q,True)
 return [0.0]+synthesis(v,q,False)[:-1]

def moment_sequence(u,apply,kmax):
 # moments <u,V^k u>, V=T* T positive. Even entries use norm squares.
 p=u[:];m=[]
 for k in range(kmax//2+1):
  m.append(inner(p,p))
  if 2*k+1<=kmax:
   vp=apply(p);m.append(inner(p,vp));p=vp
 return m[:kmax+1]

def invariants(m):
 if not m[0] or not m[1]:return {}
 c=[(v/m[0])/((m[1]/m[0])**k) for k,v in enumerate(m)]
 return {'mass':m[0],'mean':m[1]/m[0], 'scale_free_moments':c,
  'log_convex_ratios':[m[k-1]*m[k+1]/m[k]**2 for k in range(1,len(m)-1)]}

def job(args):
 b,N,kind,source,kmax=args;q=1/math.sqrt(b)
 if source=='delta0':u=[1.0]+[0.0]*(N-1)
 elif source=='delta1':u=[0.0,1.0]+[0.0]*(N-2)
 elif source=='return_value':u=[q**n for n in range(N)]
 elif source=='return_slope':u=[n*q**n for n in range(N)]
 elif source=='return_sum':u=[(n+1)*q**n for n in range(N)]
 elif source=='return_difference':u=[(1-n)*q**n for n in range(N)]
 elif source=='green_impulse':u=[n*q**n for n in range(N)]
 elif source=='depth_log_modulation':u=[q**n*math.log(n+2) for n in range(N)]
 else:raise ValueError(source)
 if kind=='analysis_gram':t=causal
 elif kind=='synthesis_gram':t=synthesis
 elif kind=='green_gram':t=green
 else:raise ValueError(kind)
 apply=lambda x:t(t(x,q,False),q,True)
 m=moment_sequence(u,apply,kmax)
 return {'family':kind,'base':b,'q':q,'N':N,'source':source,'moments':m,**invariants(m)}

def compact_mixed(kmax):
 vals=[Fraction(6,139*(k+1))*(33-8*Fraction(2,3)**(k+1)-9*Fraction(1,2)**(k+1)) for k in range(kmax+1)]
 m=list(map(float,vals));return {'family':'mixed_346_compact','variable':'v=x/6=exp(-xi)',
  'exact_moments':[str(v) for v in vals],'moments':m,**invariants(m)}

def full_camera_trace(kmax):
 # Trace state I/6 on the six-camera POVM: pure ranks1,2,1,1 and mixed rank1.
 # The compact observable is x/7 for the common support(0,7].
 vals=[]
 for k in range(kmax+1):
  mix=Fraction(33*6**(k+1)-8*4**(k+1)-9*3**(k+1),139*(k+1))
  pure=Fraction(3**k+2*4**k+5**k+7**k,k+1)
  vals.append((pure+mix)/Fraction(6*7**k))
 m=list(map(float,vals))
 return {'family':'full_camera_trace_compact','variable':'v=x/7','source':'trace I/6, ranks 1,2,1,1,1 of pure3,4,5,7,mixed', 'exact_moments':[str(v) for v in vals],'moments':m,**invariants(m)}

def pure_camera(kmax):
 vals=[Fraction(1,k+1) for k in range(kmax+1)];m=list(map(float,vals))
 return {'family':'pure_camera_compact','variable':'v=x/b','exact_moments':[str(v) for v in vals],'moments':m,**invariants(m)}

def depth_family(b,kind,kmax,N=4096):
 r=1/b
 # P(K=k)=(1-r)r^k is the exact saturated-depth distribution starting at0.
 if kind=='mass_observable':m=[(1-r)/(1-r**(k+1)) for k in range(kmax+1)]
 elif kind=='inverse_depth_square':
  m=[math.fsum((1-r)*r**n/(n+1)**(2*k) for n in range(N)) for k in range(kmax+1)]
 elif kind=='inverse_logcell_square':
  m=[math.fsum((1-r)*r**n/math.log(n+2)**(2*k) for n in range(N)) for k in range(kmax+1)]
 else:raise ValueError(kind)
 return {'family':'depth_'+kind,'base':b,'N':N,'moments':m,**invariants(m)}

def verify():
 for b in (2,3,5):
  q=1/math.sqrt(b);v=[math.sin(k+1) for k in range(20)];w=[math.cos(k+1) for k in range(20)]
  assert max(abs(x-y) for x,y in zip(causal(synthesis(v,q),q),v))<3e-14
  assert abs(inner(causal(v,q),w)-inner(v,causal(w,q,True)))<3e-14
  assert abs(inner(synthesis(v,q),w)-inner(v,synthesis(w,q,True)))<3e-14
  assert abs(inner(green(v,q),w)-inner(v,green(w,q,True)))<3e-14
  aq=causal(v,q);bq=[0.0]+[v[k+1]/q-2*v[k]+q*v[k-1] for k in range(1,len(v)-1)]
  # Aq head + interior bracket, with the final row aligned rather than dropped.
  assert max(abs(aq[n+2]-bq[n+1]) for n in range(len(v)-2))<1e-14
 print('exact-definition numerical operator checks passed',flush=True)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',required=True);ap.add_argument('--workers',type=int,default=12);ap.add_argument('--kmax',type=int,default=12)
 ar=ap.parse_args();verify();jobs=[(b,N,kind,source,ar.kmax) for b in (2,3,4,5,6,7) for N in (64,128,256,512) for kind in ('analysis_gram','synthesis_gram','green_gram') for source in ('delta0','delta1','return_value','return_slope','return_sum','return_difference','depth_log_modulation')]
 with concurrent.futures.ProcessPoolExecutor(max_workers=min(ar.workers,16)) as ex:results=list(ex.map(job,jobs,chunksize=8))
 results += [compact_mixed(ar.kmax),full_camera_trace(ar.kmax),pure_camera(ar.kmax)]
 results += [depth_family(b,kind,ar.kmax) for b in (2,3,4,5,6,7) for kind in ('mass_observable','inverse_depth_square','inverse_logcell_square')]
 out={'schema':'carry-geometric-candidates-v1','status':'geometry_fixed_no_target_input','kmax':ar.kmax,'workers':min(ar.workers,16),
  'source_note':'q and return modes are literal CPFormal definitions; depth_log_modulation=q^n log(n+2) is an explicit exploratory combination, not a native material-cell logarithmic jet or a located completed-state theorem',
  'finite_boundary':'A_N,Synthesis_N,G_N use a hard wall atN. Differences acrossN test this boundary; no uniform/infinite assertion is made from finiteprecision.',
  'normalization':'raw sources retained. scale_free_moments=m_k/m0/(m1/m0)^k are diagnostic invariants, not a fitted construction.',
  'results':results}
 Path(ar.output).write_text(json.dumps(out,indent=2));print('written',ar.output,'rows',len(results),flush=True)
if __name__=='__main__':main()
