#!/usr/bin/env python3
"""Non-rigorous Cauchy/DFT diagnostic for the shifted c8 ceiling.

This evaluates the completed xi characteristic directly, without zeros. It is
only a numerical cross-check; no interval arithmetic or Lean proof is used.
Requires mpmath.
"""

import mpmath as mp


def xi(z):
    s = mp.mpf("0.5") + z
    return mp.mpf("0.5") * s * (s - 1) * mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def coeffs_from_cauchy_dft(count, samples, radius):
    # Values on |z|=radius for Xi(1/2 + i z). The Cauchy trapezoid rule
    # returns the even Taylor coefficients; finite sampling is approximate.
    vals = [
        xi(1j * radius * mp.e ** (2 * mp.pi * 1j * j / samples))
        for j in range(samples)
    ]
    coeffs = []
    for n in range(count):
        k = 2 * n
        coeff = sum(
            vals[j] * mp.e ** (-2 * mp.pi * 1j * k * j / samples)
            for j in range(samples)
        ) / samples / radius**k
        coeffs.append(mp.re(coeff))
    return coeffs


def determinant(matrix):
    return mp.det(mp.matrix(matrix))


def probe(samples, radius):
    mp.mp.dps = 80
    c = coeffs_from_cauchy_dft(10, samples, mp.mpf(radius))

    # Division-free logarithmic derivative recurrence
    # c0 Hq = -(q+1)c(q+1) - sum_{k<q} Hk c(q-k).
    h = []
    for q in range(9):
        h.append((-(q + 1) * c[q + 1] - sum(h[k] * c[q - k] for k in range(q))) / c[0])

    tau13 = determinant([[h[1 + i + j] for j in range(3)] for i in range(3)])
    tau14 = determinant([[h[1 + i + j] for j in range(4)] for i in range(4)])
    # From R_1,3 = c0 * tau14/tau13 = 8*(ceiling - c8).
    ceiling = c[8] + c[0] * tau14 / (8 * tau13)
    return c[8], ceiling, ceiling - c[8], tau13, tau14


def main():
    for samples, radius in ((128, "1.5"), (256, "2")):
        c8, ceiling, margin, tau13, tau14 = probe(samples, radius)
        print(f"N={samples}, radius={radius}")
        print("c8       =", mp.nstr(c8, 30))
        print("ceiling  =", mp.nstr(ceiling, 30))
        print("margin   =", mp.nstr(margin, 20))
        print("tau_1,3  =", mp.nstr(tau13, 18))
        print("tau_1,4  =", mp.nstr(tau14, 18))


if __name__ == "__main__":
    main()
