#!/usr/bin/env python3
"""External Arb certificates for an a priori modal rule and source margins.

K(n)=n+2. L=||Q||_coeff,1 * exp(-(n+3)^2) is specified before inspecting R.
The infinite-mode error estimate is analytic, documented alongside this script.
Finite certificates do not establish the all-n coercive lower bound.
"""
import argparse,hashlib,importlib.util,json,math,sys
from pathlib import Path
from flint import arb,arb_mat,ctx
sys.dont_write_bytecode=True
p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--max-n',type=int,default=16);p.add_argument('--bits',type=int,default=768);p.add_argument('--output',type=Path,required=True);p.add_argument('--replication',type=Path)
a=p.parse_args();ctx.prec=a.bits;assert 0<=a.max_n<=21 and a.bits>=384
src=a.repo/'research/native-kernel-series-2026-10-14/certificate-1024.json';data=json.loads(src.read_text());engpath=a.repo/'scripts/certify_native_negative_channel.py'
assert hashlib.sha256(engpath.read_bytes()).hexdigest()==data['theta_engine_sha256']
for name,digest in data['source_lean_sha256'].items():assert hashlib.sha256((a.repo/'CarrySelfAdjointOperator'/name).read_bytes()).hexdigest()==digest
spec=importlib.util.spec_from_file_location('source',engpath);eng=importlib.util.module_from_spec(spec);spec.loader.exec_module(eng)
count=2*a.max_n+2;raw=[arb(row['infinite_integral'])for row in data['source_moments_and_tails'][:count+1]];assert len(raw)==count+1
c,m=eng.log_coefficients(raw,count)
P=[]
for j in range(count):
 coeff=[arb(0)]*(j+2);coeff[-1]=arb((-1)**j)*(j+1)/math.factorial(2*j+2)
 for k in range(j):
  for d,b in enumerate(P[k]):coeff[d]-=c[j-k]*b
 P.append([b/c[0]for b in coeff])
pi=arb.pi();r2=(arb(3)/2)**6*(-5*pi).exp();q4=16*(-3*pi).exp();assert 0<r2<arb(1)/100 and 0<q4<arb(1)/100
assert (1-r2)*(1-q4)>arb(1)/2
records=[]
for n in range(a.max_n+1):
 for s in range(2):
  if n:
   H=arb_mat([[m[i+j+s]for j in range(n)]for i in range(n)]);b=arb_mat([[m[i+n+s]]for i in range(n)]);solution=H.solve(b)
   assert all(solution[i,0].is_finite()for i in range(n));residual=H*solution-b;assert all(residual[i,0].contains(0)for i in range(n))
   v=[-solution[i,0]for i in range(n)]+[arb(1)];schur=m[2*n+s]-sum(m[i+n+s]*solution[i,0]for i in range(n))
  else:v=[arb(1)];schur=m[s]
  Q=[arb(0)]*(2*n+s+2)
  for i in range(n+1):
   for j in range(n+1):
    for d,pcoef in enumerate(P[i+j+s]):Q[d]+=c[0]*v[i]*v[j]*pcoef
  M=sum(abs(q)for q in Q);assert M>0
  degree=4*n+2*s+2;J=n+3;lam=2*pi*J*J-degree-arb(13)/2;assert lam>0
  error=32*pi**3*J**6*(-pi*J*J).exp()*M/((1-r2)*(1-q4)*lam**2)
  L=M*(-arb(J*J)).exp();margin=(4*n+2*s+3)*c[0]*schur
  # |A-margin| <= error, so margin-error >= L certifies A >= L.
  excess=margin-error-L
  assert excess>0,(n,s,str(excess));assert error<L/2
  row={'n':n,'sector':s,'K':n+2,'degree':degree,'R':str(c[0]*schur),'coefficient_l1':str(M),'specified_L':str(L),'analytic_infinite_tail_bound':str(error),'margin_minus_tail_minus_L':str(excess),'margin_over_L':str(margin/L),'tail_over_L':str(error/L),'certified_main_ge_L':True,'certified_tail_lt_L_half':True,'Q_coefficients_in_y_u_squared':[str(x)for x in Q]}
  records.append(row);print(json.dumps({k:row[k]for k in ['n','sector','K','margin_over_L','tail_over_L']}),flush=True)
res={'status':'EXTERNAL_ARB_FINITE_ADAPTIVE_SOURCE_MARGIN_CERTIFIED','bits':a.bits,'max_n':a.max_n,'rule':'K(n)=n+2, both sectors','margin_target':'L=coefficient_l1(Q_s,n)*exp(-(n+3)^2), specified independently of pivot sign','geometric_error':'32*pi^3*J^6*M*exp(-pi*J^2)/((1-r2)*(1-q4)*(2*pi*J^2-degree-13/2)^2), J=n+3','source_certificate_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'engine_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'new_quadrature':False,'source_intervals_reused':True,'all_n_margin_proved':False,'numeric_intervals_used_as_Lean_premises':False,'rows':records}
if a.replication:
 old=json.loads(a.replication.read_text());assert old['engine_sha256']==res['engine_sha256'] and old['source_certificate_sha256']==res['source_certificate_sha256']
 for x,y in zip(old['rows'],records):
  assert (x['n'],x['sector'])==(y['n'],y['sector'])
  for name in ['R','coefficient_l1','specified_L','analytic_infinite_tail_bound','margin_minus_tail_minus_L','margin_over_L','tail_over_L']:assert arb(x[name]).overlaps(arb(y[name]))
 res['different_precision_replication_overlaps']=True
a.output.write_text(json.dumps(res,indent=2)+'\n')
