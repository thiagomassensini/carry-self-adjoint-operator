#!/usr/bin/env python3
"""C2 types of odd numbers and arithmetically selected subsets.

Finite experiment only. Twin-prime asymptotic equidistribution is not proven.
C2 effective depth of an odd n = max(v2(n-1), v2(n+1)).
The twin center depth v2(p+1) is a different statistic.
"""
import math
import sys
import numpy as np

limit = int(sys.argv[1]) if len(sys.argv) > 1 else 12_000_000
isprime = np.ones(limit+1, dtype=bool)
isprime[:2] = False
for d in range(2, math.isqrt(limit)+1):
    if isprime[d]:
        isprime[d*d::d] = False
odd = np.arange(3, limit-1, 2, dtype=np.int64)
primes = odd[isprime[odd]]
eligible = primes[(primes >= 5) & (primes+2 <= limit)]
twin_lower = eligible[isprime[eligible+2]]
isolated = eligible[~(isprime[eligible-2] | isprime[eligible+2])]
composites = odd[~isprime[odd]]

def v2(a):
    return np.rint(np.log2(np.bitwise_and(a, -a))).astype(np.int64)

def c2_odd_type(n):
    return np.maximum(v2(n-1), v2(n+1))

print('limit',limit,'all_odd',len(odd),'composites',len(composites),
      'isolated_primes',len(isolated),'twin_pairs',len(twin_lower))
sets=[('all_odd',odd),('composites',composites),
      ('isolated_primes',isolated),('twin_lower_primes',twin_lower)]
for name,values in sets:
    k=c2_odd_type(values)
    print('\n',name)
    for depth in range(2,10):
        expected=2.0**(1-depth)
        count=int(np.count_nonzero(k==depth))
        observed=count/len(values)
        print('k',depth,'expected',f'{expected:.8f}',
              'observed',f'{observed:.8f}',
              'delta_pp',f'{100*(observed-expected):+.5f}',
              'count',count)
print('\nTwin center depth v2(p+1), which starts at k=1:')
kv=v2(twin_lower+1)
for depth in range(1,10):
    expected=2.0**(-depth)
    count=int(np.count_nonzero(kv==depth))
    print('k',depth,'expected',f'{expected:.8f}',
          'observed',f'{count/len(kv):.8f}','count',count)
