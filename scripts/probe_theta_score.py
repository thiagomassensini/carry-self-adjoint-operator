#!/usr/bin/env python3
"""Exploratory score transport of the unchanged source; no interval claim."""
import argparse,json
from pathlib import Path
import mpmath as mp
from flint import arb,ctx
p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--dps',type=int,default=65);p.add_argument('--modes',type=int,default=10);p.add_argument('--max-n',type=int,default=2);p.add_argument('--min-n',type=int,default=0);p.add_argument('--sector',type=int,choices=[0,1]);p.add_argument('--prefix-modes',type=int,default=1);p.add_argument('--output',type=Path,required=True)
a=p.parse_args();mp.mp.dps=a.dps;ctx.prec=1024
rows=json.loads((a.repo/'research/native-kernel-series-2026-10-14/certificate-1024.json').read_text())['source_moments_and_tails']
K=2*a.max_n+1
A=[mp.mpf(arb(r['infinite_integral']).mid().str(a.dps+10,radius=False))for r in rows[:K+2]]
c=[mp.mpf(1)/2-A[0]/4]+[(-1)**j*(A[j-1]/mp.factorial(2*j-2)-A[j]/(4*mp.factorial(2*j)))for j in range(1,len(A))]
m=[];P=[]
for j in range(K+1):
 m.append((-(j+1)*c[j+1]-sum(m[k]*c[j-k]for k in range(j)))/c[0])
 coeff=[mp.mpf(0)]*(j+2);coeff[-1]=mp.mpf((-1)**j)*(j+1)/mp.factorial(2*j+2)
 for k in range(j):
  for d,b in enumerate(P[k]):coeff[d]-=c[j-k]*b
 P.append([b/c[0]for b in coeff])
assert c[0]>0 and m[0]>0 and m[1]>0 and m[0]*m[2]>m[1]**2 and m[1]*m[3]>m[2]**2

def weight(j,u):
 q=mp.pi*j*j*mp.exp(2*u)
 return 4*mp.pi*j*j*mp.exp(mp.mpf('2.5')*u)*(2*q-3)*mp.exp(-q)
def score(j,u):
 q=mp.pi*j*j*mp.exp(2*u)
 return u*(2*q-mp.mpf('4.5')-6/(2*q-3))
def phi(u):return sum(weight(j,u)for j in range(1,a.modes+1))
def prefix_weight(u):return sum(weight(j,u)for j in range(1,a.prefix_modes+1))
def prefix_score(u):return sum(score(j,u)*weight(j,u)for j in range(1,a.prefix_modes+1))/prefix_weight(u)
def delta_density(u):
 v=prefix_score(u)
 return sum((score(j,u)-v)*weight(j,u)for j in range(a.prefix_modes+1,a.modes+1))
def geometric_bound(u):
 J=a.prefix_modes+1;p=mp.pi*mp.exp(2*u)
 ratio=mp.mpf(J+1)**6/J**6*mp.exp(-mp.pi*(2*J+1))
 return 4*p*u*J**6*mp.exp(-(J*J-1)*p)/(1-ratio)
def Qval(Q,u):return mp.polyval(Q[::-1],u*u)
def integrate(fun,cuts):return sum(mp.quad(fun,[lo,(lo+hi)/2,hi])for lo,hi in zip(cuts,cuts[1:]))
out=[]
for s in ([a.sector]if a.sector is not None else range(2)):
 for n in range(a.min_n,a.max_n+1):
  v=list(-mp.lu_solve(mp.matrix([[m[i+j+s]for j in range(n)]for i in range(n)]),mp.matrix([m[i+n+s]for i in range(n)])))+[mp.mpf(1)]if n else [mp.mpf(1)]
  Q=[mp.mpf(0)]*(2*n+s+2)
  for i in range(n+1):
   for j in range(n+1):
    for d,b in enumerate(P[i+j+s]):Q[d]+=c[0]*v[i]*v[j]*b
  k=next(k for k,x in enumerate(Q)if x)
  roots=mp.polyroots(Q[k:][::-1],maxsteps=5000,error=False)
  cuts=[mp.mpf(0)]+sorted(mp.sqrt(r.real)for r in roots if abs(r.imag)<mp.mpf(10)**(-a.dps//2)and 0<r.real<9)+[mp.mpf(3)]
  R=c[0]*sum(v[i]*v[j]*m[i+j+s]for i in range(n+1)for j in range(n+1))
  square=2*c[0]*sum(v[i]*m[i]for i in range(n+1))**2 if s else mp.mpf(0)
  approx=square+integrate(lambda u:prefix_score(u)*Qval(Q,u)*phi(u),cuts)
  correction=integrate(lambda u:Qval(Q,u)*delta_density(u),cuts)
  exact_abs_error=integrate(lambda u:abs(Qval(Q,u))*delta_density(u),cuts)
  # The proposed E_theta bound keeps the FULL Phi weight.
  envelope_error=integrate(lambda u:abs(Qval(Q,u))*delta_density(u)*phi(u)/prefix_weight(u),cuts)
  geometric_error=integrate(lambda u:abs(Qval(Q,u))*geometric_bound(u)*phi(u),cuts)
  lhs=(4*n+2*s+3)*R
  rel=abs(lhs-approx-correction)/abs(lhs)
  assert rel<mp.mpf(10)**(-a.dps//2), (s,n,mp.nstr(rel))
  vals={'sector':s,'n':n,'source_R':R,'transport_margin':lhs,'prefix_mode_score_with_full_weight_plus_square':approx,'signed_modal_correction':correction,'exact_absolute_modal_error':exact_abs_error,'Etheta_full_weight_error':envelope_error,'exact_error_over_margin':exact_abs_error/lhs,'Etheta_error_over_margin':envelope_error/lhs,'geometric_error_over_margin':geometric_error/lhs,'geometric_lower_bound':approx-geometric_error,'relative_identity_error':rel,'lower_bound':approx-envelope_error}
  row={k:(mp.nstr(v,35)if isinstance(v,mp.mpf)else v)for k,v in vals.items()};out.append(row);print(json.dumps(row),flush=True)
a.output.write_text(json.dumps({'status':'EXPLORATORY_NOT_INTERVAL_NOT_LEAN','dps':a.dps,'modes':a.modes,'prefix_modes':a.prefix_modes,'cutoff':3,'source':'unchanged source moment recurrence; thetaTail moments converted before use','rows':out},indent=2)+'\n')
