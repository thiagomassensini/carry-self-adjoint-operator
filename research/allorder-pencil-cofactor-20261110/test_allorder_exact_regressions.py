#!/usr/bin/env python3
"""Exact finite regressions for arbitrary-sequence Hankel identities.

These Fraction checks exercise the Lean identities on concrete signed,
singular, positive, zero, and indefinite inputs. They do not establish a
universal theorem; the Lean declarations supply the all-order proof.
"""

from fractions import Fraction as F
from random import Random


def det(a):
    a = [row[:] for row in a]
    n = len(a)
    out = F(1)
    for k in range(n):
        p = next((i for i in range(k, n) if a[i][k] != 0), None)
        if p is None:
            return F(0)
        if p != k:
            a[k], a[p] = a[p], a[k]
            out = -out
        pivot = a[k][k]
        out *= pivot
        for i in range(k + 1, n):
            q = a[i][k] / pivot
            for j in range(k + 1, n):
                a[i][j] -= q * a[k][j]
            a[i][k] = F(0)
    return out


def hankel(h, s, n, offset=0):
    return [[h(s + i + j + offset) for j in range(n)] for i in range(n)]


def tau(h, s, n):
    return det(hankel(h, s, n))


def adjugate(a):
    n = len(a)
    if n == 0:
        return []
    return [[((-1) ** (i + j)) * det(
        [[a[r][c] for c in range(n) if c != i]
         for r in range(n) if r != j])
        for j in range(n)] for i in range(n)]


def cofactor_vector(h, s, n):
    g = hankel(h, s, n)
    if n == 0:
        return [F(1)]
    a = adjugate(g)
    b = [h(s + n + i) for i in range(n)]
    return [-sum(a[i][j] * b[j] for j in range(n)) for i in range(n)] + [det(g)]


def check(h, s, n):
    v = cofactor_vector(h, s, n)
    big = hankel(h, s, n + 1)
    tnext = tau(h, s, n + 1)

    # Cofactor orthogonality and the exact critical-vector energy.
    w = [sum(big[i][j] * v[j] for j in range(n + 1)) for i in range(n + 1)]
    assert w == [F(0)] * n + [tnext]
    energy = sum(v[i] * big[i][j] * v[j]
                 for i in range(n + 1) for j in range(n + 1))
    assert energy == tau(h, s, n) * tnext
    for a in range(n):
        assert sum(v[j] * h(s + a + j) for j in range(n + 1)) == 0

    # Equality of the two degree-at-most-n polynomials, checked at n+1 exact
    # rational points (finite regression only).
    g = hankel(h, s, n)
    k = hankel(h, s, n, offset=1)
    for x in range(n + 1):
        lhs = sum(v[j] * F(x) ** j for j in range(n + 1))
        pencil = [[F(x) * g[i][j] - k[i][j] for j in range(n)] for i in range(n)]
        assert lhs == det(pencil)

    if n >= 1:
        lhs = tau(h, s, n) * tau(h, s + 2, n) - tau(h, s + 1, n) ** 2
        rhs = tau(h, s, n + 1) * tau(h, s + 2, n - 1)
        assert lhs == rhs


def main():
    def positive(k):
        return sum(w * x**k for w, x in ((F(1), F(1, 2)),
                                          (F(2), F(2, 3)),
                                          (F(3), F(3, 4)),
                                          (F(1), F(4, 5))))

    def negative_pivot(k):
        # First three values are the GoN control with tau_2 = -18;
        # later values merely complete a total sequence for the regression.
        prefix = (F(1), F(5), F(7))
        if k < len(prefix):
            return prefix[k]
        return F((-1) ** k * (k % 5))

    def rank_one(k):
        return F(2, 3) ** (k + 1)

    def all_zero(_k):
        return F(0)

    def indefinite(k):
        return F(1) if k % 4 == 0 else F(-1) if k % 4 == 2 else F(0)

    rng = Random(1102026)
    def random_signed(k):
        return random_values[k]

    random_values = [F(rng.randint(-7, 7), rng.randint(1, 11)) for _ in range(24)]
    cases = {
        "positive-atomic": positive,
        "negative-pivot": negative_pivot,
        "rank-one-singular": rank_one,
        "zero-determinants": all_zero,
        "indefinite": indefinite,
        "random-signed": random_signed,
    }

    assert tau(positive, 0, 1) > 0 and tau(positive, 0, 4) > 0
    assert tau(negative_pivot, 0, 2) < 0
    assert tau(rank_one, 0, 2) == 0
    assert tau(all_zero, 0, 1) == 0
    assert det(hankel(indefinite, 0, 2)) < 0

    total = 0
    for name, h in cases.items():
        for n in range(7):
            for s in range(3):
                check(h, s, n)
                total += 1
        print(f"PASS {name}: dimensions 0..6, shifts 0..2")
    print(f"PASS {total} exact Fraction cases")


if __name__ == "__main__":
    main()
