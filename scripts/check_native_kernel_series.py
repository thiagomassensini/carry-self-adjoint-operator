#!/usr/bin/env python3
"""Replay the continuous-grid certificate and audit its source transport.

The analytic identifications in the accompanying report remain outside Lean.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import sys
from flint import arb, arb_mat, ctx

sys.dont_write_bytecode = True


def main(args):
    spec = importlib.util.spec_from_file_location('series_certificate',args.engine)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    root = args.engine.resolve().parents[1]
    source = mod.load_source_engine(root)
    data = json.loads(args.certificate.read_text())
    other = json.loads(args.replication.read_text())
    assert data['status'] == other['status'] == 'EXTERNAL_CONTINUOUS_GRID_CERTIFICATE_NOT_LEAN'
    assert data['engine_sha256'] == other['engine_sha256'] == hashlib.sha256(args.engine.read_bytes()).hexdigest()
    theta_hash = hashlib.sha256((root/'scripts/certify_native_negative_channel.py').read_bytes()).hexdigest()
    assert data['theta_engine_sha256'] == other['theta_engine_sha256'] == theta_hash
    assert data['source_lean_sha256'] == other['source_lean_sha256']
    for name,digest in data['source_lean_sha256'].items():
        assert hashlib.sha256((root/'CarrySelfAdjointOperator'/name).read_bytes()).hexdigest() == digest
    assert not data['uses_cached_moments'] and not data['uses_zero_data']
    ctx.prec = 1200
    moments = [arb(r['infinite_integral']) for r in data['source_moments_and_tails']]
    for i,m in enumerate(moments):
        assert m.overlaps(arb(other['source_moments_and_tails'][i]['infinite_integral']))
    M = data['terms']
    c,h = source.log_coefficients(moments,M)
    for n in range(M):
        assert (c[0]*h[n]+sum(h[k]*c[n-k] for k in range(n))+(n+1)*c[n+1]).contains(0)
        assert h[n].overlaps(arb(data['log_moment_enclosures'][n]))
        assert h[n].overlaps(arb(other['log_moment_enclosures'][n]))
    # Independent binomial evaluation of normalized differences of monomials.
    maxN = max(case['N'] for case in data['continuous_grid_cases'])
    st = mod.stirling_table(2*M)
    for a in range(maxN):
        for p in range(2*M):
            direct = sum((-1)**(a-j)*math.comb(a,j)*(j+1)**p for j in range(a+1))
            assert direct == math.factorial(a)*st[p+1][a+1]
    # A new positive cosh remainder is integrated, separately from both runs.
    Y = arb(3)/8
    rem,rem_record = source.theta_moment(2*M+2,20,256,Y)
    def native_values(y):
        A = sum(moments[j]*y**(2*j)/math.factorial(2*j) for j in range(M+1))
        Ay = sum(moments[j]*y**(2*j-1)/math.factorial(2*j-1) for j in range(1,M+1))
        A += source.positive_interval((y**(2*M+2)/math.factorial(2*M+2)*rem).upper())
        Ay += source.positive_interval((y**(2*M+1)/math.factorial(2*M+1)*rem).upper())
        G = arb(1)/2-(arb(1)/4-y*y)*A
        Gy = 2*y*A-(arb(1)/4-y*y)*Ay
        assert G > 0 and Gy+G > 0
        r = Gy/G
        return r,(Gy-G)/(Gy+G)
    cases = []
    for case in data['continuous_grid_cases']:
        N = case['N']
        H = Q(case['H'])
        P = mod.kernel_polynomial(h,N)
        W = arb_mat([[mod.ball(x) for x in row] for row in case['auxiliary_congruence_exact_rationals']])
        assert all(W[i,i] > 0 for i in range(N))
        assert all(W[i,j] == 0 for i in range(N) for j in range(i+1,N))
        baseline,poly,tail,rho = mod.range_bound(P,W,N,H)
        assert rho < mod.ball(Q(3,4)) and case['k_plus_one_min']*H == 1
        gamma = (1-rho)/sum(W[i,j]**2 for i in range(N) for j in range(N))
        assert gamma > 0
        # Direct ORIGINAL return: incident H/h, quotient q, amplitudes and
        # binomial chart, retaining all N*N mixed entries. No Stirling input.
        direct_checks = []
        for hs in [H,H/2]:
            hh = mod.ball(hs)
            values = [native_values((i+1)*hh) for i in range(N)]
            incident = arb_mat([[arb(1)/(i+j+2)/hh for j in range(N)] for i in range(N)])
            defect = arb_mat([[incident[i,j]*(1-values[i][1]*values[j][1])
                               for j in range(N)] for i in range(N)])
            chart = arb_mat([[(1+values[i][0])/arb(2).sqrt()*
                             (-1)**(a-i)*math.comb(a,i)/(math.factorial(a)*hh**a)
                             if i <= a else arb(0) for a in range(N)] for i in range(N)])
            original_Q = chart.transpose()*defect*chart
            series_Q = sum((p*hh**d for d,p in enumerate(P)),arb_mat(N,N))
            for a in range(N):
                for b in range(N):
                    radius = mod.ball(mod.entry_tail(M,N,H,a,b))
                    enclosure = series_Q[a,b]+arb(0,radius.upper())
                    assert enclosure.overlaps(original_Q[a,b]), ('source transport mismatch',N,hs,a,b)
            direct_checks.append({'h':str(hs),'all_original_storage_entries_overlap_series':True})
        cases.append({'N':N,'k_min':case['k_min'],'relative_error_upper':str(rho.upper()),
                      'infinite_tail_upper':str(tail.upper()),'margin_lower':str(gamma.lower()),
                      'direct_original_source_chart_checks':direct_checks})
    result = {'status':'PASS_EXTERNAL_CONTINUOUS_GRID_AUDIT_NOT_LEAN',
              'source_and_engine_hashes_checked':True,'independent_run_moments_overlap':True,
              'binomial_Stirling_integer_identity_checked_through_degree':2*M-1,
              'continuous_cases_replayed':cases,'fresh_cosh_tail':rem_record,
              'analytic_series_transport_lean_proved':False,
              'analytic_infinite_tail_argument_lean_proved':False,
              'is_lean_positivity_theorem':False}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['fresh_cosh_tail']},indent=2))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--engine',type=Path,required=True)
    p.add_argument('--certificate',type=Path,required=True)
    p.add_argument('--replication',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    main(p.parse_args())
