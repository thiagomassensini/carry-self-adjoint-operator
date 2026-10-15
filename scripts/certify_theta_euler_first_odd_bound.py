#!/usr/bin/env python3
"""Outward Arb test of a candidate source bound, on the actual first odd density.

D(u)=u Q'(u)=m0*u^2-u^4/3. We certify its positive mass, retain the exact
signed integral, and disprove M_minus(D) < 2*c0*m0^2 for THIS source.
This is external finite evidence, not a Lean premise or all-order no-go.
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
    A = m[0]
    remainder = c0*m[1]
    assert remainder > 0 and (remainder-(mu1**2/(4*c0)-mu2/12)).contains(0)
    zero = (3*A).sqrt()
    lo,hi = zero.lower(),zero.upper()
    assert 0 < lo and lo <= hi and hi < 1
    pi = arb.pi()
    def finite_kernel(u):
        return sum(4*acb(pi)*j*j*(5*u/2).exp()*
                   (2*acb(pi)*j*j*(2*u).exp()-3)*
                   (-acb(pi)*j*j*(2*u).exp()).exp()
                   for j in range(1,args.modes+1))
    def density(u,analytic):
        return (acb(A)*u**2-u**4/3)*finite_kernel(u)
    finite = acb.integral(density,0,lo)
    assert finite.is_finite() and finite.imag.contains(0) and finite.real > 0
    # For 0<=u<=hi and L=M+1:
    # phi_tail <= 8*pi^2*exp(9*hi/2)*sum_(j>=0)(L+j)^4 exp(-pi*(L+j)^2).
    # (L+j)^2>=L^2+(2L+1)j, (L+j)^4<=L^4*(j+1)^4.
    L = args.modes+1
    q = (-pi*(2*L+1)).exp()
    geometric_fourth = (1+11*q+11*q*q+q**3)/(1-q)**5
    phi_tail = 8*pi*pi*(9*hi/2).exp()*L**4*(-pi*L*L).exp()*geometric_fourth
    polynomial_bound = abs(A)*hi**2+hi**4/3
    modal_error = lo*polynomial_bound*phi_tail
    short_interval = lo.union(hi)
    edge_polynomial_bound = abs(A*short_interval**2-short_interval**4/3)
    edge_phi_bound = abs(finite_kernel(acb(short_interval)).real)+phi_tail
    endpoint_error = (hi-lo)*edge_polynomial_bound*edge_phi_bound
    positive_mass = finite.real+engine.positive_interval((modal_error+endpoint_error).upper())
    square_channel = 2*c0*m[0]**2
    signed_euler_integral = A*mu1-mu2/3
    assert (signed_euler_integral-(4*remainder-square_channel)).contains(0)
    negative_mass = positive_mass-signed_euler_integral
    assert negative_mass > square_channel and square_channel > 0
    excess = negative_mass-square_channel
    result = {'status':'EXTERNAL_ARB_FIRST_ODD_SIMPLE_EULER_BOUND_REFUTED',
              'bits':args.bits,'theta_modes':args.modes,'new_source_mass_quadrature':True,
              'new_source_moment_integration':False,
              'source_coefficient_input':'published 1024-bit original theta intervals',
              'source_certificate_sha256':hashlib.sha256(source_path.read_bytes()).hexdigest(),
              'density_polynomial':'m0*u^2-u^4/3',
              'source_c0':str(c0),'source_mu1':str(mu1),'source_mu2':str(mu2),
              'positive_to_negative_transition_u':str(zero),
              'finite_positive_mass_quadrature':str(finite),
              'omitted_theta_mode_error_upper':str(modal_error.upper()),
              'uncertain_endpoint_error_upper':str(endpoint_error.upper()),
              'positive_mass':str(positive_mass),'negative_mass':str(negative_mass),
              'source_remainder':str(remainder),'square_channel':str(square_channel),
              'signed_euler_integral':str(signed_euler_integral),
              'negative_mass_minus_square':str(excess),
              'negative_mass_over_square':str(negative_mass/square_channel),
              'simple_bound_refuted':True,
              'negative_over_positive_mass':str(negative_mass/positive_mass),
              'relative_net_margin':str(signed_euler_integral/positive_mass),
              'engine_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'is_lean_numeric_proof':False,'all_order_positivity_proved':False}
    if args.replication:
        other = json.loads(args.replication.read_text())
        assert result['engine_sha256'] == other['engine_sha256']
        assert result['source_certificate_sha256'] == other['source_certificate_sha256']
        for name in ['positive_mass','negative_mass','source_remainder',
                     'positive_to_negative_transition_u','negative_mass_minus_square','negative_mass_over_square']:
            assert arb(result[name]).overlaps(arb(other[name]))
        result['different_precision_and_modes_replication_overlaps'] = True
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'bits':args.bits,
                      'zero':zero.str(15),'positive_mass':positive_mass.str(15),
                      'negative_mass':negative_mass.str(15),'remainder':remainder.str(15),
                      'negative_mass_over_square':(negative_mass/square_channel).str(15),
                      'negative_mass_minus_square':excess.str(15)},indent=2))


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
