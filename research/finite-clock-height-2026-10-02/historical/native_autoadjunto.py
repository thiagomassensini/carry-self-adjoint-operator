import mpmath as mp
from concurrent.futures import ProcessPoolExecutor
from collections import defaultdict
import os

DPS = 500
DIGITS = 80
ORDER = 40
CAMERA = 8 
CUTOFF = 25
COUNT = 40

#DPS = 2500
#DIGITS = 500
#ORDER = 80
#CAMERA = 3
#CUTOFF = 50
#COUNT = 1


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def sub(a, b):
    return a[0] - b[0], a[1] - b[1]


def mul(a, b):
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def scale(a, c):
    return a[0] * c, a[1] * c


def inv(a):
    d = a[0] * a[0] + a[1] * a[1]
    return a[0] / d, -a[1] / d


def div(a, b):
    return mul(a, inv(b))


def quarter(k):
    r = k % 4
    if r == 0:
        return mp.mpf(1), mp.mpf(0)
    if r == 1:
        return mp.mpf(0), mp.mpf(1)
    if r == 2:
        return mp.mpf(-1), mp.mpf(0)
    return mp.mpf(0), mp.mpf(-1)


def zeros(degree):
    return [(mp.mpf(0), mp.mpf(0)) for _ in range(degree + 1)]


def series_add(a, b):
    return [add(x, y) for x, y in zip(a, b)]


def series_sub(a, b):
    return [sub(x, y) for x, y in zip(a, b)]


def series_scale(a, c):
    return [scale(x, c) for x in a]


def series_mul(a, b, degree):
    out = zeros(degree)
    for n in range(degree + 1):
        total = mp.mpf(0), mp.mpf(0)
        for k in range(n + 1):
            if k < len(a) and n - k < len(b):
                total = add(total, mul(a[k], b[n - k]))
        out[n] = total
    return out


def series_div(a, b, degree):
    out = zeros(degree)
    out[0] = div(a[0], b[0])
    for n in range(1, degree + 1):
        correction = mp.mpf(0), mp.mpf(0)
        for k in range(1, n + 1):
            if k < len(b):
                correction = add(correction, mul(b[k], out[n - k]))
        out[n] = div(sub(a[n], correction), b[0])
    return out


def pair_exp(a):
    magnitude = mp.exp(a[0])
    return magnitude * mp.cos(a[1]), magnitude * mp.sin(a[1])


def series_exp(g, degree):
    out = zeros(degree)
    out[0] = pair_exp(g[0])
    for n in range(1, degree + 1):
        total = mp.mpf(0), mp.mpf(0)
        for k in range(1, n + 1):
            total = add(total, scale(mul(g[k], out[n - k]), k))
        out[n] = scale(total, mp.mpf(1) / n)
    return out


def rotation_series(amplitude, angular_rate, degree):
    out = zeros(degree)
    for k in range(degree + 1):
        coefficient = amplitude * mp.power(angular_rate, k) / mp.factorial(k)
        out[k] = scale(quarter(k), coefficient)
    return out


def native_state_series(n, degree):
    return rotation_series(1 / mp.sqrt(n), -mp.log(n), degree)


def camera_geometry(camera):
    if camera == 2:
        return 4, (1,), (1,)
    half = camera // 2
    values = tuple(range(1, half + 1))
    return camera, values, values


def compute_moment_for_k(k, period, radii, cutoff):
    mp.mp.dps = DPS

    def integrand(x):
        if x == 0:
            return mp.mpf(0)
        bracket = mp.fsum(
            4 * mp.sinh(mp.mpf(radius) * x / 2) ** 2
            for radius in radii
        )
        weight = (
            mp.exp(-period * (cutoff + 1) * x)
            * bracket
            / (-mp.expm1(-period * x))
        )
        return (
            mp.power(x, mp.mpf("-0.5"))
            * mp.power(mp.log(x), k)
            * weight
        )

    return mp.quad(integrand, [0, 1, mp.inf])


def compute_native_for_n(n, degree):
    mp.mp.dps = DPS
    return native_state_series(n, degree)


def _tail_moment_worker(args):
    k, period, radii, cutoff = args
    return compute_moment_for_k(k, period, radii, cutoff)


def finite_camera_series(camera, cutoff, degree):
    period, seeds, radii = camera_geometry(camera)
    weights = defaultdict(lambda: mp.mpf(0))

    for n in seeds:
        weights[n] += mp.mpf(1)

    for index in range(1, cutoff + 1):
        center = period * index
        weights[center] -= 2 * len(radii)
        for radius in radii:
            weights[center - radius] += mp.mpf(1)
            weights[center + radius] += mp.mpf(1)

    unique_ns = list(weights.keys())

    workers = min(os.cpu_count(), len(unique_ns))
    with ProcessPoolExecutor(max_workers=workers) as executor:
        series_list = list(executor.map(
            compute_native_for_n,
            unique_ns,
            [degree] * len(unique_ns)
        ))

    out = zeros(degree)
    for n, series in zip(unique_ns, series_list):
        if weights[n] != 0:
            out = series_add(out, series_scale(series, weights[n]))
    return out


def tail_numerator_series(camera, cutoff, degree):
    period, _, radii = camera_geometry(camera)
    args = [(k, period, radii, cutoff) for k in range(degree + 1)]

    workers = min(os.cpu_count(), len(args))
    with ProcessPoolExecutor(max_workers=workers) as executor:
        moments = list(executor.map(_tail_moment_worker, args))

    out = zeros(degree)
    for k, value in enumerate(moments):
        out[k] = scale(quarter(k), value / mp.factorial(k))
    return out


def gamma_series(real_axis, time_scale, degree, reciprocal=False):
    logarithm = zeros(degree)
    logarithm[0] = mp.log(mp.gamma(real_axis)), mp.mpf(0)

    for k in range(1, degree + 1):
        coefficient = (
            mp.polygamma(k - 1, real_axis)
            * mp.power(time_scale, k)
            / mp.factorial(k)
        )
        logarithm[k] = scale(quarter(k), coefficient)

    if reciprocal:
        logarithm = series_scale(logarithm, -1)

    return series_exp(logarithm, degree)


def exact_tail_series(camera, cutoff, degree):
    numerator = tail_numerator_series(camera, cutoff, degree)
    reciprocal_gamma = gamma_series(
        mp.mpf("0.5"), mp.mpf(1), degree, reciprocal=True
    )
    return series_mul(numerator, reciprocal_gamma, degree)


def camera_factor_series(camera, degree):
    period, _, radii = camera_geometry(camera)
    one = zeros(degree)
    one[0] = mp.mpf(1), mp.mpf(0)

    if camera == 2:
        term2 = rotation_series(
            mp.power(2, mp.mpf("-0.5")), -mp.log(2), degree
        )
        term4 = rotation_series(
            mp.power(4, mp.mpf("-0.5")), -mp.log(4), degree
        )
        return series_sub(series_sub(one, term2), series_scale(term4, 2))

    if camera % 2:
        term = rotation_series(
            mp.sqrt(period), -mp.log(period), degree
        )
        return series_sub(one, term)

    half = max(radii)
    half_term = rotation_series(
        mp.power(half, mp.mpf("-0.5")), -mp.log(half), degree
    )
    period_term = rotation_series(
        mp.power(period, mp.mpf("-0.5")), -mp.log(period), degree
    )
    return series_sub(
        series_add(one, half_term),
        series_scale(period_term, camera + 2),
    )


def completion_series(degree):
    polynomial = zeros(degree)
    polynomial[0] = mp.mpf("-0.25"), mp.mpf(0)
    if degree >= 2:
        polynomial[2] = mp.mpf(-1), mp.mpf(0)

    pi_rotation = rotation_series(
        mp.power(mp.pi, mp.mpf("-0.25")),
        -mp.log(mp.pi) / 2,
        degree,
    )

    gamma = gamma_series(
        mp.mpf("0.25"), mp.mpf("0.5"), degree
    )

    return series_scale(
        series_mul(
            series_mul(polynomial, pi_rotation, degree),
            gamma,
            degree,
        ),
        mp.mpf("0.5"),
    )


def closed_native_series(camera, cutoff, degree):
    finite = finite_camera_series(camera, cutoff, degree)
    tail = exact_tail_series(camera, cutoff, degree)
    closed = series_add(finite, tail)
    factor = camera_factor_series(camera, degree)
    common = series_div(closed, factor, degree)
    return series_mul(completion_series(degree), common, degree)


def logarithmic_moments(phi, count):
    moments = []

    for degree in range(count):
        correction = mp.fsum(
            moments[index] * phi[degree - index]
            for index in range(degree)
        )
        moments.append(
            (-(degree + 1) * phi[degree + 1] - correction) / phi[0]
        )

    return moments


def hankel_pair(moments, order):
    gram = mp.matrix(order, order)
    shifted = mp.matrix(order, order)

    for row in range(order):
        for column in range(order):
            gram[row, column] = moments[row + column]
            shifted[row, column] = moments[row + column + 1]

    return gram, shifted


def build_operator():
    degree = 4 * ORDER
    characteristic = closed_native_series(CAMERA, CUTOFF, degree)
    phi = [characteristic[2 * k][0] for k in range(2 * ORDER + 1)]
    moments = logarithmic_moments(phi, 2 * ORDER)
    gram, shifted = hankel_pair(moments, ORDER)

    cholesky = mp.cholesky(gram)
    inverse_cholesky = cholesky ** -1
    jacobi = inverse_cholesky * shifted * inverse_cholesky.T
    jacobi = (jacobi + jacobi.T) / 2

    spectrum, vectors = mp.eigsy(jacobi)
    heights = sorted(1 / mp.sqrt(value) for value in spectrum)

    diagonal = mp.diag([1 / mp.sqrt(value) for value in spectrum])
    operator = vectors * diagonal * vectors.T

    return heights, operator


def main():
    mp.mp.dps = DPS
    heights, _ = build_operator()

    for value in heights[:COUNT]:
        print(mp.nstr(value, DIGITS))


if __name__ == "__main__":
    main()
