#!/usr/bin/env python3
"""Numerical exploration: remove the algebraic TOP-coefficient balance
from signed native Schur cross-curvature; display remaining compensation.

The exact analytic identity is in SchurCurvatureGate.lean. The numbers in
coefficients.json are not rigorous intervals. No zero heights are inputs.
"""
import json
import math
import sys

import mpmath as mp


if len(sys.argv) != 2:
    raise SystemExit("usage: probe_compensation.py <coefficients.json>")
mp.mp.dps = 1750
h = [mp.mpf(x) for x in json.load(open(sys.argv[1]))["canonical_h"]]
N = min(128, len(h)//2)
Q = {}
for parity in (0, 1):
    A = [[h[parity+i+j] for j in range(N)] for i in range(N)]
    pivots = []
    for i in range(N):
        pivot = A[i][i]
        pivots.append(pivot)
        row = A[i][i+1:]
        for j in range(i+1, N):
            factor = row[j-i-1]/pivot
            for k in range(j, N):
                A[j][k] -= factor*row[k-i-1]
            for k in range(j+1, N):
                A[k][j] = A[j][k]
    Q[parity] = pivots

print("columns: dyadic block; rms(original); rms(normalized compensation); rms(top coefficient)")
for j in range(1, math.floor(math.log2(N-2))+1):
    lo, hi = 2**j, min(2**(j+1)-1, N-2)
    measured, compensated, top_alone = [], [], []
    for n in range(lo, hi+1):
        real_odd = Q[0][n]*Q[0][n+1]/Q[1][n]**2
        real_even = Q[1][n]*Q[1][n-1]/Q[0][n]**2
        symbol_odd = mp.mpf(2*n+1)*(4*n+3)/(2*(n+1)*(4*n+5))
        symbol_even = mp.mpf(2*n)*(4*n+1)/((2*n+1)*(4*n+3))
        measured.extend([float(abs(real_odd-1)), float(abs(real_even-1))])
        compensated.extend([float(abs(real_odd/symbol_odd-1)),
                             float(abs(real_even/symbol_even-1))])
        top_alone.extend([float(abs(symbol_odd-1)), float(abs(symbol_even-1))])
    def rms(vals):
        return math.sqrt(sum(x*x for x in vals)/len(vals))
    print(j, f"{lo}-{hi}", *(f"{rms(v):.9f}" for v in
                               (measured, compensated, top_alone)),
          "normalization compensation x2^(j/2)=",
          f"{rms(compensated)*2**(j/2):.6f}", flush=True)
