import math,json,time
import numpy as np
start=time.monotonic();P=10_000_000
sieve=bytearray(b'\1')*(P+1);sieve[0:2]=b'\0\0'
for p in range(2,math.isqrt(P)+1):
 if sieve[p]:
  a=p*p;sieve[a:P+1:p]=b'\0'*((P-a)//p+1)
primes=np.asarray([p for p in range(2,P+1) if sieve[p]],dtype=np.float64)

def ratios(h):return {'R2':h[0]*h[2]/h[1]**2,'R3':h[0]**2*h[3]/h[1]**3,'R_adj':h[1]*h[3]/h[2]**2}
def bounds(lo,hi):return {'R2':[lo[0]*lo[2]/hi[1]**2,hi[0]*hi[2]/lo[1]**2], 'R3':[lo[0]**2*lo[3]/hi[1]**3,hi[0]**2*hi[3]/lo[1]**3], 'R_adj':[lo[1]*lo[3]/hi[2]**2,hi[1]*hi[3]/lo[2]**2]}
rows=[]
for cutoff in [1_000_000,10_000_000]:
 pp=primes[primes<=cutoff];lam=1/((pp-1)*np.log(pp)**2)
 m=[math.fsum(lam**k) for k in range(1,5)]
 tail=[cutoff/(cutoff-1)/math.log(cutoff)]
 for k in range(2,5):tail.append((cutoff/(cutoff-1))**k/((k-1)*cutoff**(k-1)*math.log(cutoff)**(2*k)))
 lo=[v-1e-10 for v in m];hi=[m[i]+tail[i]+1e-10 for i in range(4)]
 rows.append({'cutoff':cutoff,'count':len(pp),'moments_prefix':m,'all_integer_tail_bound':tail,'ratios_prefix':ratios(m),'ratio_bounds':bounds(lo,hi)})
# m0 reused from independent Euler--Maclaurin audit by agent notas_retorno.
m0_text='2.109742801236891974479257197616551326385531984394742022649915603192814694939136874177169291377186232'
natural=[float(m0_text)];blocks=[[],[],[]]
for begin in range(2,P+1,1_000_000):
 ns=np.arange(begin,min(P+1,begin+1_000_000),dtype=np.float64);lam=1/(ns*np.log(ns)**2)
 for j,k in enumerate(range(2,5)):blocks[j].append(math.fsum(lam**k))
natural += [math.fsum(b) for b in blocks]
ntail=[0.0]+[1/((k-1)*P**(k-1)*math.log(P)**(2*k)) for k in range(2,5)]
lo=[v-1e-10 for v in natural];hi=[natural[i]+ntail[i]+1e-10 for i in range(4)]
result={'workers':1,'prime_rank_one_fibers':rows,'material_numbers':{'cutoff':P,'m0_reused':m0_text,'moments':natural,'analytic_tail_bound':ntail,'ratios':ratios(natural),'ratio_bounds':bounds(lo,hi),'m0_source':'/home/thlinux/carry-kernel-geometric-search-20260904/graph/geometric_diagonal_candidates.json; candidates[0].moments[0]'},'elapsed_seconds':time.monotonic()-start}
print(json.dumps(result,indent=2))
