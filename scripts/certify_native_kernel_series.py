#!/usr/bin/env python3
"""External Arb proof of a CONTINUOUS grid range for the unchanged source.

The coefficient majorant is kernel-checked in Lean. The analytic series
identification and its Stirling finite-difference transport are documented
mathematics, not Lean proofs. No target Gram or zero data enters the source.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import sys
import time
from flint import arb, arb_mat, ctx

sys.dont_write_bytecode = True
ALPHA = Q(22, 175)


def load_source_engine(root):
    path = root/'scripts/certify_native_negative_channel.py'
    spec = importlib.util.spec_from_file_location('original_theta_source', path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def ball(q):
    q = Q(q)
    return arb(q.numerator)/q.denominator


def stirling_table(top):
    table = [[0]*(top+1) for _ in range(top+1)]
    table[0][0] = 1
    for p in range(1, top+1):
        for a in range(1, p+1):
            table[p][a] = a*table[p-1][a]+table[p-1][a-1]
    return table


def kernel_polynomial(h, N):
    """Exact finite differences of the first M native kernel terms."""
    M = len(h)
    assert M >= N
    st = stirling_table(2*M)
    matrices = [[[arb(0) for _ in range(N)] for _ in range(N)]
                for _ in range(2*M-1)]
    for a in range(N):
        for b in range(N):
            for n in range((a+b+1)//2, M):
                integer = sum((-1)**(n+q)*st[2*n-q+1][a+1]*st[q+1][b+1]
                              for q in range(b, 2*n-a+1))
                matrices[2*n-a-b][a][b] = 2*h[n]*integer
    return list(map(arb_mat, matrices))


def rational_boundary_congruence(B):
    """Auxiliary proof matrix only; never changes the original features."""
    N = B.nrows()
    lower = [[arb(int(i == j)) for j in range(N)] for i in range(N)]
    pivots = []
    for j in range(N):
        d = B[j,j]-sum(lower[j][s]**2*pivots[s] for s in range(j))
        assert d > 0, ('unresolved boundary sign', N, j, str(d))
        pivots.append(d)
        for i in range(j+1, N):
            lower[i][j] = (B[i,j]-sum(lower[i][s]*lower[j][s]*pivots[s]
                                    for s in range(j)))/d
    L = arb_mat([[lower[i][j]*pivots[j].sqrt() for j in range(N)] for i in range(N)])
    enclosure = L.inv()
    # Every entry is now an EXACT dyadic rational, with no interval dependency.
    rational = [[str(enclosure[i,j].mid().fmpq()) for j in range(N)] for i in range(N)]
    W = arb_mat([[ball(x) for x in row] for row in rational])
    assert all(W[i,i] > 0 for i in range(N))
    assert all(W[i,j] == 0 for i in range(N) for j in range(i+1,N))
    return W, rational, pivots


def entry_tail(M, N, H, a, b):
    """Exact rational infinite-series majorant, including h=0."""
    R = N*H
    z = ALPHA*R*R
    d = a+b+1
    assert 2*M+2 > d
    ratio = z*Q((2*M+3)*(2*M+2), (2*M+3-d)*(2*M+2-d))
    assert 0 < z < 1 and 0 < ratio < 1
    return 2*ALPHA*R**(-a-b)*math.comb(2*M+1, d)*z**M/(1-ratio)


def matrix_abs(A):
    return arb_mat([[abs(A[i,j]) for j in range(A.ncols())] for i in range(A.nrows())])


def max_row_sum(A):
    bound = arb(0)
    for i in range(A.nrows()):
        bound = bound.max(sum(abs(A[i,j]) for j in range(A.ncols())))
    return bound


def range_bound(P, W, N, H):
    Nmat = W*P[0]*W.transpose()-arb_mat([[int(i == j) for j in range(N)] for i in range(N)])
    baseline = max_row_sum(Nmat)
    Pnorm = [max_row_sum(W*p*W.transpose()) for p in P[1:]]
    polynomial = sum((v*ball(H)**(d+1) for d,v in enumerate(Pnorm)), arb(0))
    T = arb_mat([[ball(entry_tail((len(P)+1)//2,N,H,a,b))
                  for b in range(N)] for a in range(N)])
    tail = max_row_sum(matrix_abs(W)*T*matrix_abs(W).transpose())
    return baseline, polynomial, tail, baseline+polynomial+tail


def certify(args):
    ctx.prec = args.bits
    started = time.monotonic()
    engine = load_source_engine(args.repo_root)
    records = []
    moments = []
    for j in range(args.terms+1):
        value, record = engine.theta_moment(2*j,args.modes,args.cutoff)
        moments.append(value)
        records.append(record)
        print('fresh theta moment',2*j,flush=True)
    _, h = engine.log_coefficients(moments,args.terms)
    cases = []
    for N in args.dimensions:
        P = kernel_polynomial(h,N)
        W, rational, pivots = rational_boundary_congruence(P[0])
        for exponent in range(4,128):
            H = Q(1,2**exponent)
            if N*H > Q(1,4):
                continue
            baseline,poly,tail,rho = range_bound(P,W,N,H)
            if rho < ball(Q(3,4)):
                break
        else:
            raise AssertionError(('no certified range found',N))
        frobenius = sum(W[i,j]**2 for i in range(N) for j in range(N))
        gamma = (1-rho)/frobenius
        assert gamma > 0
        cases.append({'N':N,'H':str(H),'k_plus_one_min':2**exponent,
                      'k_min':2**exponent-1,'continuous_h_range':'0 <= h <= H',
                      'boundary_LDL_pivots':list(map(str,pivots)),
                      'auxiliary_congruence_exact_rationals':rational,
                      'boundary_identity_error_row_norm_upper':str(baseline.upper()),
                      'polynomial_error_row_norm_upper':str(poly.upper()),
                      'infinite_tail_row_norm_upper':str(tail.upper()),
                      'total_relative_error_upper':str(rho.upper()),
                      'original_coefficient_energy_margin_lower':str(gamma.lower()),
                      'all_original_complex_inputs':True,
                      'original_negative_Jordan_port_zero_on_grid_range':True})
        print('CONTINUOUS RANGE',N,2**exponent-1,'rho',rho.str(15),flush=True)
    names = ['CompletedNativeRadialChiralMultiplier.lean',
             'CompletedNativeChiralJetStorageTransport.lean',
             'CompletedNativeChiralEvenBoundaryEnergy.lean',
             'CompletedNativeXiThetaCosineRepresentation.lean',
             'CompletedNativeAllOrderMomentUpperBound.lean',
             'CompletedNativeLogCoefficientMajorant.lean',
             'CompletedNativeChiralReturnBoundaryCoefficientProvenance.lean']
    result = {'status':'EXTERNAL_CONTINUOUS_GRID_CERTIFICATE_NOT_LEAN',
              'precision_bits':args.bits,'terms':args.terms,'modes':args.modes,
              'cutoff':args.cutoff,'alpha':'22/175','source_moments_and_tails':records,
              'log_moment_enclosures':list(map(str,h)),'continuous_grid_cases':cases,
              'source_features_metric_amplitudes_unchanged':True,
              'uses_cached_moments':False,'uses_zero_data':False,
              'kernel_coefficient_majorant_lean_proved':True,
              'analytic_series_transport_lean_proved':False,
              'engine_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'theta_engine_sha256':hashlib.sha256((args.repo_root/'scripts/certify_native_negative_channel.py').read_bytes()).hexdigest(),
              'source_lean_sha256':{name:hashlib.sha256((args.repo_root/'CarrySelfAdjointOperator'/name).read_bytes()).hexdigest()
                                    for name in names},
              'elapsed_seconds':time.monotonic()-started}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('saved',args.output,flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo-root',type=Path,default=Path(__file__).resolve().parents[1])
    parser.add_argument('--bits',type=int,default=768)
    parser.add_argument('--terms',type=int,default=40)
    parser.add_argument('--modes',type=int,default=16)
    parser.add_argument('--cutoff',type=int,default=256)
    parser.add_argument('--dimensions',type=int,nargs='+',default=[8,10,12])
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    assert args.bits >= 512 and args.terms >= max(args.dimensions)
    assert args.modes >= 1 and args.cutoff >= 4 and min(args.dimensions) >= 1
    certify(args)
