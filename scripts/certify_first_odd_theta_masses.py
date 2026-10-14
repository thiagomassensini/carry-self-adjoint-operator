#!/usr/bin/env python3
"""Fresh Arb quadrature of the FIRST odd source's positive/negative masses.

Source coefficients replay the published 1024-bit theta certificate. Only
the positive-mass integral is newly integrated; the negative mass follows
from the exact signed identity and the source remainder. This is external
finite evidence, not an all-order positivity proof or a Lean numeric premise.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from flint import arb, acb, ctx

sys.dont_write_bytecode = True


def main(args):
    ctx.prec = args.bits
    root = args.repo_root
    source_path = root/'research/native-kernel-series-2026-10-14/certificate-1024.json'
    data = json.loads(source_path.read_text())
    engine_path = root/'scripts/certify_native_negative_channel.py'
    assert hashlib.sha256(engine_path.read_bytes()).hexdigest() == data['theta_engine_sha256']
    for name,digest in data['source_lean_sha256'].items():
        assert hashlib.sha256((root/'CarrySelfAdjointOperator'/name).read_bytes()).hexdigest() == digest
    spec = importlib.util.spec_from_file_location('theta_source',engine_path)
    engine = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(engine)
    theta = [arb(r['infinite_integral']) for r in data['source_moments_and_tails'][:3]]
    c,m = engine.log_coefficients(theta,2)
    c0 = c[0]
    mu1 = -2*c[1]
    mu2 = 24*c[2]
    A = mu1/(4*c0)
    remainder = c0*m[1]
    assert remainder > 0 and (remainder-(mu1**2/(4*c0)-mu2/12)).contains(0)
    zero = (3*mu1/c0).sqrt()
    lo,hi = zero.lower(),zero.upper()
    assert 0 < lo and lo <= hi and hi < 1
    pi = arb.pi()
    def finite_kernel(u):
        return sum(4*acb(pi)*j*j*(5*u/2).exp()*
                   (2*acb(pi)*j*j*(2*u).exp()-3)*
                   (-acb(pi)*j*j*(2*u).exp()).exp()
                   for j in range(1,args.modes+1))
    def density(u,analytic):
        return (acb(A)*u**2-u**4/12)*finite_kernel(u)
    finite = acb.integral(density,0,lo)
    assert finite.is_finite() and finite.imag.contains(0) and finite.real > 0
    # For 0<=u<=hi and L=M+1:
    # phi_tail <= 8*pi^2*exp(9*hi/2)*sum_(j>=0)(L+j)^4 exp(-pi*(L+j)^2).
    # (L+j)^2>=L^2+(2L+1)j, (L+j)^4<=L^4*(j+1)^4.
    L = args.modes+1
    q = (-pi*(2*L+1)).exp()
    geometric_fourth = (1+11*q+11*q*q+q**3)/(1-q)**5
    phi_tail = 8*pi*pi*(9*hi/2).exp()*L**4*(-pi*L*L).exp()*geometric_fourth
    polynomial_bound = abs(A)*hi**2+hi**4/12
    modal_error = lo*polynomial_bound*phi_tail
    short_interval = lo.union(hi)
    edge_polynomial_bound = abs(A*short_interval**2-short_interval**4/12)
    edge_phi_bound = abs(finite_kernel(acb(short_interval)).real)+phi_tail
    endpoint_error = (hi-lo)*edge_polynomial_bound*edge_phi_bound
    positive_mass = finite.real+engine.positive_interval((modal_error+endpoint_error).upper())
    negative_mass = positive_mass-remainder
    assert negative_mass > 0 and positive_mass > negative_mass
    result = {'status':'EXTERNAL_ARB_FIRST_ODD_THETA_MASSES_NOT_ALL_ORDER_POSITIVITY',
              'bits':args.bits,'theta_modes':args.modes,'new_source_mass_quadrature':True,
              'new_source_moment_integration':False,
              'source_coefficient_input':'published 1024-bit original theta intervals',
              'source_certificate_sha256':hashlib.sha256(source_path.read_bytes()).hexdigest(),
              'density_polynomial':'mu1/(4*c0)*u^2-u^4/12',
              'source_c0':str(c0),'source_mu1':str(mu1),'source_mu2':str(mu2),
              'positive_to_negative_transition_u':str(zero),
              'finite_positive_mass_quadrature':str(finite),
              'omitted_theta_mode_error_upper':str(modal_error.upper()),
              'uncertain_endpoint_error_upper':str(endpoint_error.upper()),
              'positive_mass':str(positive_mass),'negative_mass':str(negative_mass),
              'source_remainder':str(remainder),
              'negative_over_positive_mass':str(negative_mass/positive_mass),
              'relative_net_margin':str(remainder/positive_mass),
              'engine_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'is_lean_numeric_proof':False,'all_order_positivity_proved':False}
    if args.replication:
        other = json.loads(args.replication.read_text())
        assert result['engine_sha256'] == other['engine_sha256']
        assert result['source_certificate_sha256'] == other['source_certificate_sha256']
        for name in ['positive_mass','negative_mass','source_remainder',
                     'positive_to_negative_transition_u','negative_over_positive_mass']:
            assert arb(result[name]).overlaps(arb(other[name]))
        result['different_precision_and_modes_replication_overlaps'] = True
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'bits':args.bits,
                      'zero':zero.str(15),'positive_mass':positive_mass.str(15),
                      'negative_mass':negative_mass.str(15),'remainder':remainder.str(15),
                      'relative_net_margin':(remainder/positive_mass).str(15)},indent=2))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo-root',type=Path,default=Path(__file__).resolve().parents[1])
    p.add_argument('--bits',type=int,default=768)
    p.add_argument('--modes',type=int,default=16)
    p.add_argument('--replication',type=Path)
    p.add_argument('--output',type=Path,required=True)
    args = p.parse_args()
    assert args.bits >= 256 and args.modes >= 1
    main(args)
