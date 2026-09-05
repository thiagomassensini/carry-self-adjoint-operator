"""Exact polynomial audit of the C3 clock and its observation tower.
No third-party packages, sampled zeros, fitted scales or native moments.
"""
import json
from fractions import Fraction as F
from itertools import permutations
from math import log
from pathlib import Path

class P(dict):
    def __add__(self, other):
        other = poly(other)
        out = P(self)
        for k, v in other.items():
            out[k] = out.get(k, F(0)) + v
            if not out[k]: del out[k]
        return out
    __radd__ = __add__
    def __neg__(self): return P({k: -v for k,v in self.items()})
    def __sub__(self, other): return self + -poly(other)
    def __rsub__(self, other): return poly(other) + -self
    def __mul__(self, other):
        out = P()
        for e,v in self.items():
            for f,w in poly(other).items():
                k = tuple(x+y for x,y in zip(e,f))
                out = out + P({k: v*w})
        return out
    __rmul__ = __mul__
    def __pow__(self, n):
        out = poly(1)
        for _ in range(n): out = out * self
        return out

def poly(x): return x if isinstance(x, P) else P({(0,0,0): F(x)}) if x else P()
def mm(A,B): return [[sum((poly(A[i][k])*B[k][j] for k in range(len(B))), P()) for j in range(len(B[0]))] for i in range(len(A))]
def det(A):
    out=P()
    for p in permutations(range(len(A))):
        term=poly((-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p))))
        for i,j in enumerate(p): term=term*A[i][j]
        out=out+term
    return out

a,b,c = [P({tuple(int(i==j) for i in range(3)):F(1)}) for j in range(3)]
C=[[1,0,0],[-1,1,0],[0,-1,1]]
R=[[1,0,0],[1,1,0],[1,1,1]]
D=[[a,0,0],[0,b,0],[0,0,c]]
L=mm(mm(C,D),R)
expected=[[a,0,0],[b-a,b,0],[c-b,c-b,c]]
q=[[0,-1,1]]
q1=mm(q,L)
q2=mm(q1,L)
O=q+q1+q2
Q=[[1,-2,1]]
Q1=mm(Q,D)
Q2=mm(Q1,D)
checks={
    'gradient_roundtrip': mm(C,R)==[[poly(int(i==j)) for j in range(3)] for i in range(3)],
    'clock_conjugacy': L==[[poly(v) for v in row] for row in expected],
    'value_trace': mm(q,C)==[[poly(v) for v in Q[0]]],
    'pulse_instantaneous_invisible': mm(q,[[1],[0],[0]])==[[P()]],
    'pulse_log_trace': q1[0][0]==a-2*b+c,
    'observability_determinant': det(O)==-2*(b-a)*(c-a)*(c-b),
}
for j, (u,v,w) in enumerate([(a,b,c),(b,a,c),(c,a,b)]):
    row=[Q2[0][i]-(v+w)*Q1[0][i]+v*w*Q[0][i] for i in range(3)]
    target=[P(),P(),P()]
    target[j]=[1,-2,1][j]*(u-v)*(u-w)
    checks['inverse_identity_'+str(j)]=row==target
# The native affine seed generates precisely C * diag(a,b,c) * (1,1,1).
checks['affine_seed']=mm(mm(C,D),[[1],[1],[1]])==[[a],[b-a],[c-b]]
# A constant pulse on nodes 2,3,4, with its clock-matched log channel.
checks['consistent_log_trace']=mm(mm(Q,D),[[1],[1],[1]])==[[a-2*b+c]]
result={'method':'exact rational polynomial arithmetic in independent a,b,c',
        'checks':checks,'passed':all(checks.values()),
        'native_gap_float_for_orientation_only':log(2)-2*log(3)+log(4),
        'native_gap_exact':'log(8/9) < 0 since 0 < 8 < 9',
        'lean_compilation':'not performed by this Python audit'}
Path(__file__).with_name('exact_check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
assert result['passed']
