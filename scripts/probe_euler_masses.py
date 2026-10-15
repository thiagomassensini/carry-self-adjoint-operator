#!/usr/bin/env python3
"""Exploratory quadrature, never a Lean or interval positivity certificate."""
import argparse,json,math,time
from pathlib import Path
import mpmath as mp
from flint import arb,ctx
p=argparse.ArgumentParser(); p.add_argument('--repo',type=Path,required=True);p.add_argument('--dps',type=int,default=80);p.add_argument('--modes',type=int,default=12);p.add_argument('--max-n',type=int,default=2);p.add_argument('--output',type=Path,required=True)
a=p.parse_args();mp.mp.dps=a.dps;ctx.prec=1024
cert=a.repo/'research/native-kernel-series-2026-10-14/certificate-1024.json'
data=json.loads(cert.read_text()); max_index=2*a.max_n+1
A=[mp.mpf(arb(r['infinite_integral']).mid().str(a.dps+10, radius=False)) for r in data['source_moments_and_tails'][:max_index+2]]
c=[mp.mpf(1)/2-A[0]/4]+[(-1)**j*(A[j-1]/mp.factorial(2*j-2)-A[j]/(4*mp.factorial(2*j))) for j in range(1,len(A))]
assert c[0]>0
m=[]; P=[]
for j in range(max_index+1):
 m.append((-(j+1)*c[j+1]-sum(m[k]*c[j-k] for k in range(j)))/c[0])
 coeff=[mp.mpf('0')]*(j+2);coeff[-1]=mp.mpf((-1)**j)*(j+1)/mp.factorial(2*j+2)
 for k in range(j):
  for d,b in enumerate(P[k]):coeff[d]-=c[j-k]*b
 P.append([x/c[0] for x in coeff])
assert m[0]>0 and m[1]>0
if len(m)>2:assert m[0]*m[2]>m[1]**2
if len(m)>3:assert m[1]*m[3]>m[2]**2
def phi(u):
 e2=mp.exp(2*u);fac=4*mp.pi*mp.exp(mp.mpf('2.5')*u)
 return fac*sum(j*j*(2*mp.pi*j*j*e2-3)*mp.exp(-mp.pi*j*j*e2) for j in range(1,a.modes+1))
def eval_y(coeff,u): return mp.polyval(coeff[::-1],u*u)
def signed_masses(coeff):
 # Factor out the vanishing constant coefficient before finding positive roots in y=u^2.
 nz=next(k for k,x in enumerate(coeff) if x)
 roots=mp.polyroots(list(reversed(coeff[nz:])),maxsteps=5000,error=False)
 cuts=[mp.mpf('0')]+sorted(mp.sqrt(r.real) for r in roots if abs(r.imag)<mp.mpf(10)**(-a.dps//2) and r.real>0 and r.real<9)+[mp.mpf('3')]
 plus=mp.mpf('0');minus=mp.mpf('0')
 for lo,hi in zip(cuts,cuts[1:]):
  val=mp.quad(lambda u:eval_y(coeff,u)*phi(u),[lo,(lo+hi)/2,hi])
  if val>=0:plus+=val
  else:minus-=val
 return plus,minus,cuts
out=[]
for n in range(a.max_n+1):
 v=list(-mp.lu_solve(mp.matrix([[m[i+j+1] for j in range(n)]for i in range(n)]),mp.matrix([m[i+n+1] for i in range(n)])))+[mp.mpf('1')] if n else [mp.mpf('1')]
 Q=[mp.mpf('0')]*(2*n+3)
 for i in range(n+1):
  for j in range(n+1):
   for d,b in enumerate(P[i+j+1]): Q[d]+=c[0]*v[i]*v[j]*b
 D=[2*d*b for d,b in enumerate(Q)]
 rem=c[0]*sum(v[i]*v[j]*m[i+j+1] for i in range(n+1)for j in range(n+1))
 square=2*c[0]*sum(v[i]*m[i] for i in range(n+1))**2
 Dp,Dm,cuts=signed_masses(D)
 rhs=Dp-Dm+square
 row={'n':n,'s':1,'R':mp.nstr(rem,40),'square_channel':mp.nstr(square,40),'derivative_positive_mass':mp.nstr(Dp,40),'derivative_negative_mass':mp.nstr(Dm,40),'negative_over_square':mp.nstr(Dm/square,30),'relative_balance_error':mp.nstr(abs(rhs-(4*n+4)*rem)/abs((4*n+4)*rem),10),'simple_square_bound_passes':bool(Dm<square),'positive_derivative_roots_u':[mp.nstr(x,25)for x in cuts[1:-1]]}
 assert abs(rhs-(4*n+4)*rem)/abs((4*n+4)*rem) < mp.mpf(10)**(-a.dps//2), row
 out.append(row);print(json.dumps(row),flush=True)
a.output.write_text(json.dumps({'status':'EXPLORATORY_MPMATH_NOT_INTERVAL_CERTIFICATE','dps':a.dps,'theta_modes':a.modes,'cutoff':3,'raw_theta_moments':'thetaTail even-moment midpoints; converted by exact source Green formula to characteristic coefficients','rows':out},indent=2)+'\n')
