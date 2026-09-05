#!/usr/bin/env python3
"""Generate kernel-checkable rational theta certificates using only Fraction arithmetic."""
from fractions import Fraction as F
from math import factorial, floor, ceil
from pathlib import Path
import json
import argparse
parser=argparse.ArgumentParser()
parser.add_argument("--output-directory", default="/tmp/theta-five-bounds-generated")
args=parser.parse_args()
N=128

def low(x):
    return sum((x/32)**i/factorial(i) for i in range(12))**32

def up(x):
    return (sum((x/32)**i/factorial(i) for i in range(12))+(x/32)**12*F(13,factorial(12)*12))**32

def term(x):
    return f'({x.numerator}/{x.denominator}:ℝ)'

nodes={F(j,N) for j in range(N+1)}
for p in [0,2,4]:
    for j in range(N):
        a,b=F(j,N),F(j+1,N)
        mass=(b**(p+1)-a**(p+1))/(p+1)
        moment=(b**(p+2)-a**(p+2))/(p+2)
        nodes.add(moment/mass)
records=[]
out=Path(args.output_directory);out.mkdir(exist_ok=True)
for i,q in enumerate(sorted(nodes)):
    el=F(floor(low(2*q)*10**10),10**10)
    eu=F(ceil(up(2*q)*10**10),10**10)
    arglo=F(3141592,10**6)*el-q/2
    arghi=F(3141593,10**6)*eu-q/2
    l=F(floor(2/up(arghi)*10**12),10**12)
    r=F(ceil(2/low(arglo)*10**12),10**12)
    assert 0<=arglo<=arghi<=32 and 0<=l<=r
    record=dict(id=i,q=str(q),el=str(el),eu=str(eu),l=str(l),r=str(r))
    records.append(record)
    code=f'''theorem thetaFirstMode_node_{i:03d} :
    {term(l)} ≤ thetaFirstMode {term(q)} ∧ thetaFirstMode {term(q)} ≤ {term(r)} := by
  apply thetaFirstMode_node_bounds {term(q)} {term(el)} {term(eu)}
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

'''
    if i==0:
        (out/'NodeTest.lean').write_text('import CarrySelfAdjointOperator.CompletedNativeThetaExponentialBounds\nnamespace CarrySelfAdjointOperator\nset_option maxHeartbeats 4000000\n'+code+'end CarrySelfAdjointOperator\n')
    group=i//32
    dest=out/f'ThetaNodes{group:02d}.lean'
    if i%32==0:
        dest.write_text('import CarrySelfAdjointOperator.CompletedNativeThetaExponentialBounds\n\nnamespace CarrySelfAdjointOperator\nset_option maxHeartbeats 4000000\n\n')
    with dest.open('a') as f:f.write(code)
    if i%32==31 or i==len(nodes)-1:
        with dest.open('a') as f:f.write('end CarrySelfAdjointOperator\n')
(out/'nodes.json').write_text(json.dumps(records,indent=2))
print(f'{len(records)} rational node certificates generated')
