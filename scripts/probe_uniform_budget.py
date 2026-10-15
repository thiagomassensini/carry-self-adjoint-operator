import json, argparse
from pathlib import Path
import mpmath as mp
from flint import arb,ctx
p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--max-n',type=int,default=12);p.add_argument('--dps',type=int,default=150);p.add_argument('--output',type=Path,required=True)
a=p.parse_args();mp.mp.dps=a.dps;ctx.prec=1024
rows=json.loads((a.repo/'research/native-kernel-series-2026-10-14/certificate-1024.json').read_text())['source_moments_and_tails'];maxidx=2*a.max_n+1
A=[mp.mpf(arb(r['infinite_integral']).mid().str(a.dps+10,radius=False))for r in rows[:maxidx+2]]
assert len(A)==maxidx+2
c=[mp.mpf(1)/2-A[0]/4]+[(-1)**j*(A[j-1]/mp.factorial(2*j-2)-A[j]/(4*mp.factorial(2*j)))for j in range(1,len(A))]
m=[];P=[]
for j in range(maxidx+1):
 m.append((-(j+1)*c[j+1]-sum(m[k]*c[j-k]for k in range(j)))/c[0])
 pcoef=[mp.mpf(0)]*(j+2);pcoef[-1]=mp.mpf((-1)**j)*(j+1)/mp.factorial(2*j+2)
 for k in range(j):
  for d,b in enumerate(P[k]):pcoef[d]-=c[j-k]*b
 P.append([b/c[0]for b in pcoef])
r2=(mp.mpf(3)/2)**6*mp.exp(-5*mp.pi);q4=16*mp.exp(-3*mp.pi)
result=[]
for n in range(a.max_n+1):
 for s in range(2):
  v=list(-mp.lu_solve(mp.matrix([[m[i+j+s]for j in range(n)]for i in range(n)]),mp.matrix([m[i+n+s]for i in range(n)])))+[mp.mpf(1)]if n else[mp.mpf(1)]
  Q=[mp.mpf(0)]*(2*n+s+2)
  for i in range(n+1):
   for j in range(n+1):
    for d,b in enumerate(P[i+j+s]):Q[d]+=c[0]*v[i]*v[j]*b
  M=sum(abs(b)for b in Q);R=c[0]*sum(v[i]*v[j]*m[i+j+s]for i in range(n+1)for j in range(n+1));C=4*n+2*s+3
  J=n+3;K=n+2;degree=4*n+2*s+2;lam=2*mp.pi*J*J-degree-mp.mpf(13)/2
  budget=32*mp.pi**3*J**6*mp.exp(-mp.pi*J*J)/((1-r2)*(1-q4)*lam**2)*M
  L=M*mp.exp(-J*J)
  row={'n':n,'sector':s,'K':K,'degree':degree,'R':mp.nstr(R,35),'coefficient_l1':mp.nstr(M,35),'target_L':mp.nstr(L,35),'tail_bound':mp.nstr(budget,35),'margin_over_L':mp.nstr(C*R/L,20),'tail_over_L':mp.nstr(budget/L,20),'source_margin_exceeds_L_plus_tail':bool(C*R>L+budget)}
  result.append(row);print(json.dumps(row),flush=True)
a.output.write_text(json.dumps({'status':'EXPLORATORY_MIDPOINT_INPUT_NOT_INTERVAL_PROOF','dps':a.dps,'rule':'K(n)=n+2','target':'L=coefficient_l1(Q)*exp(-(n+3)^2)','rows':result},indent=2)+'\n')
