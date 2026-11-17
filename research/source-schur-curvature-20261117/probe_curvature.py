#!/usr/bin/env python3
"""Read canonical moments; inspect signed *relative* cross-curvatures.

A numerical reconnaissance only: input moment strings are not interval balls;
positivity of high-order pivots is not a formal certificate. No zero heights.
"""
import json
import sys
import mpmath as mp

if len(sys.argv) != 2:
    raise SystemExit('usage: probe_curvature.py <stage_B/coefficients.json>')
data = json.load(open(sys.argv[1], encoding='utf-8'))
mp.mp.dps = 1800
h = [mp.mpf(t) for t in data['canonical_h']]
N = min(128, len(h)//2)
Q = {}
for sector in (0, 1):
    A = [[h[sector+i+j] for j in range(N)] for i in range(N)]
    q = []
    for n in range(N):
        pivot = A[n][n]
        q.append(pivot)
        row = A[n][n+1:]
        for j in range(n+1, N):
            t = row[j-n-1]/pivot
            for k in range(j, N):
                A[j][k] -= t*row[k-n-1]
            for k in range(j+1, N):
                A[k][j] = A[j][k]
    Q[sector] = q

odd = [(n, abs(Q[0][n]*Q[0][n+1]/Q[1][n]**2-1)) for n in range(N-1)]
even = [(n, abs(Q[1][n]*Q[1][n-1]/Q[0][n]**2-1)) for n in range(1, N)]
print('moments:',len(h),'precision_dps:',mp.mp.dps,'block_N:',N)
print('positive_pivots:',all(p>0 for z in Q.values() for p in z))
print('tested_cross_curvatures:',len(odd)+len(even))
for start in (0, 2, 3, 6, 25, 100):
    candidates = [('odd', n, z) for n,z in odd if n>=start]
    candidates += [('even', n, z) for n,z in even if n>=start]
    sec, n, peak = max(candidates,key=lambda x:x[2])
    print(f'n>={start}: max={mp.nstr(peak,17)} at {sec} center n={n}')
