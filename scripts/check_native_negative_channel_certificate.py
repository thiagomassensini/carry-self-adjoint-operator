#!/usr/bin/env python3
"""Audit the external certificate and compare a stronger independent run.

Also evaluates the source quotient by fresh direct theta quadrature at two
nodes, independently of the certificate's moment/Taylor evaluation.
"""
import argparse
import importlib.util
import hashlib
import json
import math
import sys
from fractions import Fraction as Q
from pathlib import Path
import flint
from flint import arb,acb,ctx


def main(args):
    sys.dont_write_bytecode=True
    spec=importlib.util.spec_from_file_location('native_certificate',args.engine)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    ctx.prec=1024
    data=json.loads(args.certificate.read_text())
    other=json.loads(args.replication.read_text())
    engine_hash=hashlib.sha256(args.engine.read_bytes()).hexdigest()
    assert data['engine_sha256']==other['engine_sha256']==engine_hash
    source_root=args.engine.resolve().parents[1]/'CarrySelfAdjointOperator'
    assert data['source_lean_sha256']==other['source_lean_sha256']
    for name,digest in data['source_lean_sha256'].items():
        assert hashlib.sha256((source_root/name).read_bytes()).hexdigest()==digest
    assert data['status']=='EXTERNAL_ARB_CERTIFICATE_NOT_LEAN'
    assert data['source_unchanged'] and not data['uses_zeta_or_zeros'] and not data['uses_cached_moments']
    moments=[arb(z['infinite_integral']) for z in data['source_moments_and_tails'][:-1]]
    _,h=mod.log_coefficients(moments,8)
    assert all(arb(d)>0 for d in data['native_boundary_K8_minus_2pow_minus90_LDL_pivots'])
    K=[[(-1)**((i+j)//2+i)*2*h[(i+j)//2] if (i+j)%2==0 else arb(0)
        for j in range(8)] for i in range(8)]
    gamma=arb(2)**-90
    mod.ldl([[K[i][j]-(gamma if i==j else 0) for j in range(8)] for i in range(8)])
    assert arb(data['normalized_odd_fourth_LDL_pivot'])>0
    for case in data['finite_return_cases']:
        N=case['N'];q=list(map(arb,case['q_enclosures']))
        H=[[arb(1)/(i+j+2) for j in range(N)] for i in range(N)]
        mod.ldl([[H[i][j]*(1-q[i]*q[j]) for j in range(N)] for i in range(N)])
    for i,m in enumerate(moments):
        assert m.overlaps(arb(other['source_moments_and_tails'][i]['infinite_integral']))
    assert arb(data['normalized_odd_fourth_LDL_pivot']).overlaps(arb(other['normalized_odd_fourth_LDL_pivot']))
    matching={(z['N'],z['k']):z for z in other['finite_return_cases']}
    for case in data['finite_return_cases']:
        second=matching[case['N'],case['k']]
        for q,qq in zip(case['q_enclosures'],second['q_enclosures']):assert arb(q).overlaps(arb(qq))
    # Rational constants in the analytic estimate (calculus proof is in the report).
    R=Q(1,4)
    source_lower=Q(1,3)-R**2/(35*(1-R**2/25))
    source_derivative=2*R/(35*(1-R**2/25)**2)
    assert source_lower==Q(926,2793)
    assert 0<source_derivative/source_lower<1
    assert Q(data['analytic_uniform_eight_source_derivation']['source_G_lower'])==source_lower
    assert Q(data['analytic_uniform_eight_source_derivation']['source_Gprime_upper'])==source_derivative
    assert 8**3*16**16==2**73
    assert Q(1,2**90)-2**73*Q(1,2**164)==Q(1,2**91)>0
    # Fresh direct quadrature, bypassing the moment Taylor evaluator.
    direct=[]
    ctx.prec=768
    modes=16;cutoff=256;pi=arb.pi()
    def direct_slope(y):
        def f(x,analytic):
            u=x.log(analytic=analytic)/2
            return u*(y*u).sinh()*(-3*u/2).exp()*sum(
                (-acb(pi)*j*j*x).exp() for j in range(1,modes+1))
        knots=[1,2,4,8,16,32,64,128,256]
        finite=sum((acb.integral(f,a,b) for a,b in zip(knots,knots[1:])),acb(0))
        assert finite.is_finite() and finite.imag.contains(0)
        spatial=mod.exp_tail(2,pi,arb(cutoff))/(2*(1-(-3*pi*cutoff).exp()))
        rate=pi*(modes+1)**2
        modal=mod.exp_tail(2,rate,arb(1))/(2*(1-(-pi*(2*modes+3)).exp()))
        return finite.real+mod.positive_interval((spatial+modal).upper())
    case=next(z for z in data['finite_return_cases'] if z['N']==8 and z['k']==31)
    for index in [0,7]:
        y=arb(index+1)/32
        A,_=mod.theta_moment(0,modes,cutoff,y)
        Ay=direct_slope(y)
        F=arb(1)/2-(arb(1)/4-y*y)*A
        Fy=2*y*A-(arb(1)/4-y*y)*Ay
        q=(Fy-F)/(Fy+F)
        assert q.overlaps(arb(case['q_enclosures'][index]))
        direct.append({'y':str(y),'direct_q':str(q),'overlaps_Taylor_enclosure':True})
    result={'status':'PASS_EXTERNAL_CERTIFICATE_AUDIT_NOT_LEAN','source_hashes_checked':True,'all_finite_LDL_rechecked':True,
            'boundary_margin_rechecked':True,'stronger_run_overlaps':True,
            'direct_theta_source_checks':direct,
            'analytic_constants_exact_rational_checks':True,
            'analytic_calculus_argument_mechanically_checked':False,
            'is_lean_proof':False}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='direct_theta_source_checks'},indent=2))


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--engine',type=Path,default=Path(__file__).with_name('certify_native_negative_channel.py'))
    p.add_argument('--certificate',type=Path,required=True)
    p.add_argument('--replication',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    main(p.parse_args())
