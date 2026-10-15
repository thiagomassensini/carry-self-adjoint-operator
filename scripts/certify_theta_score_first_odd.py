#!/usr/bin/env python3
"""External outward-Arb certificate for the source score estimate at s=1,n=0.
The analytic inequalities and tails are documented in the companion report.
No quadrature or certificate is a premise of the Lean proofs.
"""
import argparse,hashlib,importlib.util,json,sys
from pathlib import Path
from flint import arb,acb,ctx
sys.dont_write_bytecode=True
p=argparse.ArgumentParser();p.add_argument('--repo-root',type=Path,required=True);p.add_argument('--bits',type=int,default=384);p.add_argument('--modes',type=int,default=8);p.add_argument('--output',type=Path,required=True);p.add_argument('--replication',type=Path)
a=p.parse_args();assert a.bits>=256 and a.modes>=1;ctx.prec=a.bits
source=a.repo_root/'research/native-kernel-series-2026-10-14/certificate-1024.json'
data=json.loads(source.read_text());engine_path=a.repo_root/'scripts/certify_native_negative_channel.py'
assert hashlib.sha256(engine_path.read_bytes()).hexdigest()==data['theta_engine_sha256']
for name,digest in data['source_lean_sha256'].items():assert hashlib.sha256((a.repo_root/'CarrySelfAdjointOperator'/name).read_bytes()).hexdigest()==digest
spec=importlib.util.spec_from_file_location('engine',engine_path);engine=importlib.util.module_from_spec(spec);spec.loader.exec_module(engine)
c,m=engine.log_coefficients([arb(r['infinite_integral'])for r in data['source_moments_and_tails'][:3]],2)
pi=arb.pi();T=arb(3);square=2*c[0]*m[0]**2;R=c[0]*m[1];margin=5*R
assert R>0
r6=(arb(3)/2)**6*(-5*pi).exp();q4=16*(-3*pi).exp()
assert r6<1 and q4<1
# All u>=0: Phi<=8*pi^2*e^(9u/2)*e^(-p)/(1-q4),
# 0<=V-V1<= B(u)=256*p*u*e^(-3p)/(1-r6), p=pi*e^(2u).
# Proof: consecutive positive-mode ratios are bounded by the displayed
# geometric constants, using j^2-J^2 >= (2J+1)(j-J).
def phi(u):return sum(4*acb(pi)*j*j*(5*u/2).exp()*(2*acb(pi)*j*j*(2*u).exp()-3)*(-acb(pi)*j*j*(2*u).exp()).exp()for j in range(1,a.modes+1))
def V1(u):
 p=acb(pi)*(2*u).exp();return u*(2*p-acb(9)/2-6/(2*p-3))
def B(u):
 p=acb(pi)*(2*u).exp();return 256*p*u*(-3*p).exp()/acb(1-r6)
def Q(u):return acb(m[0])*u*u/2-u**4/12
def Qabs(u):return acb(abs(m[0]))*u*u/2+u**4/12
main_int=acb.integral(lambda u,analytic: V1(u)*Q(u)*phi(u),0,T)
error_int=acb.integral(lambda u,analytic: B(u)*Qabs(u)*phi(u),0,T)
assert main_int.is_finite()and error_int.is_finite()and main_int.imag.contains(0)and error_int.imag.contains(0)
L=a.modes+1;qL=(arb(L+1)/L)**4*(-pi*(2*L+1)).exp();assert qL<1
phi_omitted=8*pi*pi*(9*T/2).exp()*L**4*(-pi*L*L).exp()/(1-qL)
Qsup=abs(m[0])*T*T/2+T**4/12
Vsup=5*pi*T*(2*T).exp()
# p*exp(-3p) decreases for p>=pi, so B<=256*pi*T*exp(-3pi)/(1-r6).
Bsup=256*pi*T*(-3*pi).exp()/(1-r6)
mode_main=T*Vsup*Qsup*phi_omitted;mode_error=T*Bsup*Qsup*phi_omitted
# Integral_T^infty u^k exp(a*u-b*exp(2u)) du:
# use u^k<=T^k exp(k*(u-T)/T), exp(2u)>=exp(2T)*(1+2(u-T)).
def tail(k,linear,b):
 decay=2*b*(2*T).exp()-linear-arb(k)/T;assert decay>0
 return T**k*(linear*T).exp()*(-b*(2*T).exp()).exp()/decay
poly=[(2,abs(m[0])/2),(4,arb(1)/12)]
tail_main=40*pi**3/(1-q4)*sum(coef*tail(d+1,arb(13)/2,pi)for d,coef in poly)
tail_error=2048*pi**3/((1-r6)*(1-q4))*sum(coef*tail(d+1,arb(13)/2,4*pi)for d,coef in poly)
main_error=(mode_main+tail_main).upper()
main=square+main_int.real+(-main_error).union(main_error)
error=error_int.real+engine.positive_interval((mode_error+tail_error).upper())
assert error>0
lower=main-error
assert lower>0 and main-error<margin and margin<main+error
res={'status':'EXTERNAL_ARB_FIRST_ODD_SCORE_BOUND_CERTIFIED','bits':a.bits,'modes':a.modes,'cutoff':str(T),'source_R':str(R),'transport_margin_5R':str(margin),'first_mode_score_with_FULL_weight_plus_square':str(main),'geometric_absolute_error_upper_enclosure':str(error),'positive_lower_bound':str(lower),'error_over_margin':str(error/margin),'r6':str(r6),'q4':str(q4),'finite_main_quadrature':str(main_int),'finite_error_quadrature':str(error_int),'omitted_mode_main_error_upper':str(mode_main.upper()),'omitted_mode_bound_error_upper':str(mode_error.upper()),'infinite_interval_main_tail_upper':str(tail_main.upper()),'infinite_interval_bound_tail_upper':str(tail_error.upper()),'source_certificate_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'engine_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'numerics_are_lean_premises':False,'all_order_positivity_proved':False}
if a.replication:
 prev=json.loads(a.replication.read_text());assert prev['engine_sha256']==res['engine_sha256']
 for name in ['source_R','transport_margin_5R','first_mode_score_with_FULL_weight_plus_square','geometric_absolute_error_upper_enclosure','positive_lower_bound','error_over_margin']:assert arb(prev[name]).overlaps(arb(res[name]))
 res['replication_overlaps']=True
a.output.write_text(json.dumps(res,indent=2)+'\n');print(json.dumps({k:res[k]for k in ['status','bits','positive_lower_bound','error_over_margin']},indent=2))
