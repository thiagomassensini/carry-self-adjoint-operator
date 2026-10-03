import os
import time
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed

import mpmath as mp

# ============================================================
# CONFIGURATION
# ============================================================

DPS = int(os.getenv("NATIVE_DPS", "500"))
DIGITS = int(os.getenv("NATIVE_DIGITS", "170"))
ORDER = int(os.getenv("NATIVE_ORDER", "50"))
CAMERA = int(os.getenv("NATIVE_CAMERA", "2"))
CUTOFF = int(os.getenv("NATIVE_CUTOFF", "2"))
COUNT = int(os.getenv("NATIVE_COUNT", "10"))

PARALLEL = os.getenv("NATIVE_PARALLEL", "1") != "0"
# 0 means: use every logical CPU reported by os.cpu_count().
MAX_WORKERS = int(os.getenv("NATIVE_WORKERS", "0"))

ORDER_IDENTITY_AUDIT = os.getenv("NATIVE_ORDER_AUDIT", "1") != "0"
ORDER_AUDIT_DIGITS = int(os.getenv("NATIVE_ORDER_AUDIT_DIGITS", "60"))
PRINT_TIMINGS = os.getenv("NATIVE_TIMINGS", "1") != "0"
FUNCTIONAL_PARALLEL_MIN_ORDER = int(os.getenv("NATIVE_FUNCTIONAL_PARALLEL_MIN_ORDER", "48"))

# Optional independent tail oracle. Slow; keep disabled in production.
TAIL_REFERENCE_AUDIT = os.getenv("NATIVE_TAIL_REFERENCE_AUDIT", "0") != "0"
TAIL_REFERENCE_DEGREE = int(os.getenv("NATIVE_TAIL_REFERENCE_DEGREE", "8"))


# ============================================================
# BASIC PAIR / SERIES ARITHMETIC
# ============================================================

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
    """amplitude * exp(i * angular_rate * z), using a coefficient recurrence."""
    out = zeros(degree)
    coefficient = mp.mpf(amplitude)
    out[0] = coefficient, mp.mpf(0)
    for k in range(1, degree + 1):
        coefficient *= angular_rate / k
        out[k] = scale(quarter(k), coefficient)
    return out


def native_state_series(n, degree):
    return rotation_series(1 / mp.sqrt(n), -mp.log(n), degree)


# ============================================================
# CAMERA GEOMETRY / FINITE PART
# ============================================================

def camera_geometry(camera):
    if camera == 2:
        return 4, (1,), (1,)
    half = camera // 2
    values = tuple(range(1, half + 1))
    return camera, values, values


def finite_weight_map(camera, cutoff):
    period, seeds, radii = camera_geometry(camera)
    weights = defaultdict(int)

    for n in seeds:
        weights[n] += 1

    for index in range(1, cutoff + 1):
        center = period * index
        weights[center] -= 2 * len(radii)
        for radius in radii:
            weights[center - radius] += 1
            weights[center + radius] += 1

    return [(n, weight) for n, weight in weights.items() if weight]


def finite_chunk_series(items, degree):
    out = zeros(degree)
    for n, weight in items:
        out = series_add(
            out,
            series_scale(native_state_series(n, degree), mp.mpf(weight)),
        )
    return out


def finite_camera_series(camera, cutoff, degree):
    return finite_chunk_series(finite_weight_map(camera, cutoff), degree)


# ============================================================
# GAMMA / COMPLETION
# ============================================================

def gamma_series(real_axis, time_scale, degree, reciprocal=False):
    real_axis = mp.mpf(real_axis)
    time_scale = mp.mpf(time_scale)
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


def completion_from_gamma(gamma, degree):
    polynomial = zeros(degree)
    polynomial[0] = mp.mpf("-0.25"), mp.mpf(0)
    if degree >= 2:
        polynomial[2] = mp.mpf(-1), mp.mpf(0)

    pi_rotation = rotation_series(
        mp.power(mp.pi, mp.mpf("-0.25")),
        -mp.log(mp.pi) / 2,
        degree,
    )

    return series_scale(
        series_mul(
            series_mul(polynomial, pi_rotation, degree),
            gamma,
            degree,
        ),
        mp.mpf("0.5"),
    )


def completion_series(degree):
    gamma = gamma_series(mp.mpf("0.25"), mp.mpf("0.5"), degree)
    return completion_from_gamma(gamma, degree)


# ============================================================
# BATCH EULER--MACLAURIN HURWITZ JET
# ============================================================

def scalar_series_mul(a, b, degree):
    return [
        mp.fsum(a[j] * b[k - j] for j in range(k + 1))
        for k in range(degree + 1)
    ]


def exp_linear_taylor(rate, degree, prefactor=1):
    out = [mp.mpf(0)] * (degree + 1)
    out[0] = mp.mpf(prefactor)
    for k in range(1, degree + 1):
        out[k] = out[k - 1] * rate / k
    return out


def series_mul_linear_scalar(a, constant, degree):
    out = [mp.mpf(0)] * (degree + 1)
    out[0] = constant * a[0]
    for k in range(1, degree + 1):
        out[k] = constant * a[k] + a[k - 1]
    return out


def hurwitz_taylor(a, degree, em_terms=None):
    """Taylor jet of zeta(s,a) about s=1/2, all orders propagated together."""
    s0 = mp.mpf("0.5")
    a = mp.mpf(a)

    if em_terms is None:
        em_terms = max(16, mp.mp.prec // 3)

    head_terms = em_terms
    bernoulli_terms = em_terms
    out = [mp.mpf(0)] * (degree + 1)

    for n in range(head_terms):
        x = a + n
        rate = -mp.log(x)
        coefficient = mp.power(x, -s0)
        out[0] += coefficient
        for k in range(1, degree + 1):
            coefficient *= rate / k
            out[k] += coefficient

    endpoint = a + head_terms
    log_endpoint = mp.log(endpoint)

    exponential = exp_linear_taylor(
        -log_endpoint, degree, mp.power(endpoint, 1 - s0)
    )
    integral = [mp.mpf(0)] * (degree + 1)
    denominator0 = s0 - 1
    integral[0] = exponential[0] / denominator0
    for k in range(1, degree + 1):
        integral[k] = (exponential[k] - integral[k - 1]) / denominator0
    for k in range(degree + 1):
        out[k] += integral[k]

    endpoint_power = exp_linear_taylor(
        -log_endpoint, degree, mp.power(endpoint, -s0)
    )
    for k in range(degree + 1):
        out[k] += endpoint_power[k] / 2

    qseries = series_mul_linear_scalar(endpoint_power, s0, degree)
    inv_endpoint = 1 / endpoint
    for k in range(degree + 1):
        qseries[k] *= inv_endpoint

    factorial = mp.mpf(2)
    rising_degree = 1
    inv_endpoint_sq = inv_endpoint * inv_endpoint

    for j in range(1, bernoulli_terms + 1):
        weight = mp.bernoulli(2 * j) / factorial
        for k in range(degree + 1):
            out[k] += weight * qseries[k]

        if j != bernoulli_terms:
            qseries = series_mul_linear_scalar(
                qseries, s0 + rising_degree, degree
            )
            qseries = series_mul_linear_scalar(
                qseries, s0 + rising_degree + 1, degree
            )
            for k in range(degree + 1):
                qseries[k] *= inv_endpoint_sq
            rising_degree += 2
            factorial *= (2 * j + 1) * (2 * j + 2)

    return out


def scaled_hurwitz_taylor(base, a, degree):
    base = mp.mpf(base)
    s0 = mp.mpf("0.5")
    log_factor = -mp.log(base)
    prefactor = mp.power(base, -s0)
    exponential = exp_linear_taylor(log_factor, degree, prefactor)
    return scalar_series_mul(exponential, hurwitz_taylor(a, degree), degree)


def exact_tail_scalar_taylor(camera, cutoff, degree):
    q = mp.mpf(cutoff + 1)

    if camera == 2:
        whole = hurwitz_taylor(4 * q - 1, degree)
        even = scaled_hurwitz_taylor(2, 2 * q, degree)
        centers = scaled_hurwitz_taylor(4, q, degree)
        return [
            whole[k] - even[k] - 2 * centers[k]
            for k in range(degree + 1)
        ]

    period = mp.mpf(camera)
    half = camera // 2
    first_integer = period * q - half
    whole = hurwitz_taylor(first_integer, degree)

    if camera % 2:
        centers = scaled_hurwitz_taylor(period, q, degree)
        return [
            whole[k] - period * centers[k]
            for k in range(degree + 1)
        ]

    midpoints = scaled_hurwitz_taylor(period, q + mp.mpf("0.5"), degree)
    centers = scaled_hurwitz_taylor(period, q, degree)
    return [
        whole[k] + midpoints[k] - (period + 1) * centers[k]
        for k in range(degree + 1)
    ]


def exact_tail_series(camera, cutoff, degree):
    coefficients = exact_tail_scalar_taylor(camera, cutoff, degree)
    return [scale(quarter(k), coefficients[k]) for k in range(degree + 1)]


# ============================================================
# OPTIONAL SLOW TAIL ORACLE
# ============================================================

def tail_numerator_series_reference(camera, cutoff, degree):
    period, _, radii = camera_geometry(camera)
    moments = []

    for k in range(degree + 1):
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
        moments.append(mp.quad(integrand, [0, 1, mp.inf]))

    out = zeros(degree)
    for k, value in enumerate(moments):
        out[k] = scale(quarter(k), value / mp.factorial(k))
    return out


def exact_tail_series_reference(camera, cutoff, degree):
    numerator = tail_numerator_series_reference(camera, cutoff, degree)
    reciprocal_gamma = gamma_series(
        mp.mpf("0.5"), mp.mpf(1), degree, reciprocal=True
    )
    return series_mul(numerator, reciprocal_gamma, degree)


# ============================================================
# CAMERA FACTOR
# ============================================================

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
        term = rotation_series(mp.sqrt(period), -mp.log(period), degree)
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


# ============================================================
# PARALLEL GERM ASSEMBLY
# ============================================================

def available_workers(task_count=None):
    cpu = os.cpu_count() or 1
    workers = cpu if MAX_WORKERS <= 0 else min(cpu, MAX_WORKERS)
    if task_count is not None:
        workers = min(workers, max(1, task_count))
    return max(1, workers)


def split_items(items, chunks):
    chunks = max(1, min(chunks, len(items)))
    return [items[i::chunks] for i in range(chunks)]


def _germ_worker(kind, payload, dps):
    mp.mp.dps = dps

    if kind == "finite_chunk":
        items, degree = payload
        return finite_chunk_series(items, degree)

    if kind == "hurwitz":
        a, degree = payload
        return hurwitz_taylor(mp.mpf(a), degree)

    if kind == "scaled_hurwitz":
        base, a, degree = payload
        return scaled_hurwitz_taylor(mp.mpf(base), mp.mpf(a), degree)

    if kind == "gamma_completion":
        degree, = payload
        return gamma_series(mp.mpf("0.25"), mp.mpf("0.5"), degree)

    raise ValueError(f"unknown germ worker kind: {kind}")


def tail_task_specs(camera, cutoff, degree):
    q = mp.mpf(cutoff + 1)

    if camera == 2:
        return [
            ("whole", "hurwitz", (mp.nstr(4 * q - 1, mp.mp.dps), degree)),
            ("even", "scaled_hurwitz", ("2", mp.nstr(2 * q, mp.mp.dps), degree)),
            ("centers", "scaled_hurwitz", ("4", mp.nstr(q, mp.mp.dps), degree)),
        ]

    period = mp.mpf(camera)
    half = camera // 2
    first_integer = period * q - half
    specs = [
        ("whole", "hurwitz", (mp.nstr(first_integer, mp.mp.dps), degree)),
    ]

    if camera % 2 == 0:
        specs.append(
            ("midpoints", "scaled_hurwitz", (
                str(camera),
                mp.nstr(q + mp.mpf("0.5"), mp.mp.dps),
                degree,
            ))
        )

    specs.append(
        ("centers", "scaled_hurwitz", (
            str(camera), mp.nstr(q, mp.mp.dps), degree
        ))
    )
    return specs


def assemble_tail_from_parts(camera, degree, parts):
    if camera == 2:
        scalar = [
            parts["whole"][k] - parts["even"][k] - 2 * parts["centers"][k]
            for k in range(degree + 1)
        ]
    elif camera % 2:
        period = mp.mpf(camera)
        scalar = [
            parts["whole"][k] - period * parts["centers"][k]
            for k in range(degree + 1)
        ]
    else:
        period = mp.mpf(camera)
        scalar = [
            parts["whole"][k]
            + parts["midpoints"][k]
            - (period + 1) * parts["centers"][k]
            for k in range(degree + 1)
        ]

    return [scale(quarter(k), scalar[k]) for k in range(degree + 1)]


def closed_native_series_serial(camera, cutoff, degree):
    finite = finite_camera_series(camera, cutoff, degree)
    tail = exact_tail_series(camera, cutoff, degree)
    closed = series_add(finite, tail)
    factor = camera_factor_series(camera, degree)
    common = series_div(closed, factor, degree)
    return series_mul(completion_series(degree), common, degree)


def closed_native_series_parallel(camera, cutoff, degree):
    dps = mp.mp.dps
    finite_items = finite_weight_map(camera, cutoff)
    tail_specs = tail_task_specs(camera, cutoff, degree)

    workers = available_workers()
    # Fill otherwise-idle workers with independent finite chunks.  The batch
    # Hurwitz jets themselves remain intact, preserving their coefficient reuse.
    reserved = len(tail_specs) + 1  # tail jets + gamma completion
    finite_chunks = max(1, workers - reserved)
    chunks = split_items(finite_items, finite_chunks)

    tasks = []
    for idx, chunk in enumerate(chunks):
        tasks.append((f"finite_{idx}", "finite_chunk", (chunk, degree)))
    tasks.extend(tail_specs)
    tasks.append(("gamma", "gamma_completion", (degree,)))

    workers = available_workers(len(tasks))
    results = {}

    with ProcessPoolExecutor(max_workers=workers) as executor:
        future_to_label = {
            executor.submit(_germ_worker, kind, payload, dps): label
            for label, kind, payload in tasks
        }
        for future in as_completed(future_to_label):
            results[future_to_label[future]] = future.result()

    finite = zeros(degree)
    for idx in range(len(chunks)):
        finite = series_add(finite, results[f"finite_{idx}"])

    tail_parts = {label: results[label] for label, _, _ in tail_specs}
    tail = assemble_tail_from_parts(camera, degree, tail_parts)
    completion = completion_from_gamma(results["gamma"], degree)

    closed = series_add(finite, tail)
    factor = camera_factor_series(camera, degree)
    common = series_div(closed, factor, degree)
    return series_mul(completion, common, degree)


def closed_native_series(camera, cutoff, degree):
    if PARALLEL and available_workers() > 1:
        return closed_native_series_parallel(camera, cutoff, degree)
    return closed_native_series_serial(camera, cutoff, degree)


# ============================================================
# MOMENTS / JACOBI RECURRENCE
# ============================================================

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


def rescaled_moments(moments, scale_value):
    out = []
    power = mp.mpf(1)
    for moment in moments:
        out.append(moment * power)
        power *= scale_value
    return out


def jacobi_recurrence_coefficients(moments, order):
    """Chebyshev algorithm; beta[k] is the square of off-diagonal k."""
    width = 2 * order
    previous = [mp.mpf(0)] * width
    current = [moments[index] for index in range(width)]

    alpha = [moments[1] / moments[0]]
    beta = [moments[0]]

    for k in range(1, order):
        updated = [mp.mpf(0)] * width
        for ell in range(k, width - k):
            updated[ell] = (
                current[ell + 1]
                - alpha[k - 1] * current[ell]
                - beta[k - 1] * previous[ell]
            )

        alpha.append(
            updated[k + 1] / updated[k]
            - current[k] / current[k - 1]
        )
        beta.append(updated[k] / current[k - 1])
        previous, current = current, updated

    return alpha, beta


def self_adjointness_defects(beta):
    return [
        (index, value)
        for index, value in enumerate(beta)
        if index >= 1 and value <= 0
    ]


def jacobi_matrix(alpha, beta):
    order = len(alpha)
    matrix = mp.zeros(order, order)
    for index in range(order):
        matrix[index, index] = alpha[index]
    for index in range(1, order):
        off_diagonal = mp.sqrt(beta[index])
        matrix[index - 1, index] = off_diagonal
        matrix[index, index - 1] = off_diagonal
    return matrix


def build_moment_data(max_order, camera=CAMERA, cutoff=CUTOFF):
    degree = 4 * max_order
    characteristic = closed_native_series(camera, cutoff, degree)
    phi = [
        characteristic[2 * k][0]
        for k in range(2 * max_order + 1)
    ]
    moments = logarithmic_moments(phi, 2 * max_order)
    return characteristic, phi, moments


def recurrence_from_moments(moments, order):
    scale_value = 1 / moments[0]
    scaled = rescaled_moments(moments, scale_value)
    alpha, beta = jacobi_recurrence_coefficients(scaled, order)
    defects = self_adjointness_defects(beta)
    if defects:
        indices = [k for k, _ in defects]
        raise ArithmeticError(
            "beta_k <= 0 at indices " + str(indices)
            + "; increase precision before calling this a structural defect"
        )
    return scale_value, alpha, beta


# ============================================================
# SPECTRAL WORKERS / FUNCTIONAL CALCULUS
# ============================================================

def _spectral_worker(alpha, beta, dps):
    mp.mp.dps = dps
    matrix = jacobi_matrix(alpha, beta)
    spectrum_matrix, vectors_matrix = mp.eigsy(matrix)
    spectrum = [spectrum_matrix[i] for i in range(spectrum_matrix.rows)]
    vectors = [
        [vectors_matrix[i, j] for j in range(vectors_matrix.cols)]
        for i in range(vectors_matrix.rows)
    ]
    return spectrum, vectors


def spectral_data(alpha, beta):
    spectrum, vectors = _spectral_worker(alpha, beta, mp.mp.dps)
    return spectrum, vectors


def spectral_pair_parallel(alpha_n, beta_n, alpha_succ, beta_succ):
    dps = mp.mp.dps
    if not PARALLEL or available_workers() < 2:
        return (
            spectral_data(alpha_n, beta_n),
            spectral_data(alpha_succ, beta_succ),
        )

    with ProcessPoolExecutor(max_workers=2) as executor:
        future_n = executor.submit(_spectral_worker, alpha_n, beta_n, dps)
        future_s = executor.submit(_spectral_worker, alpha_succ, beta_succ, dps)
        return future_n.result(), future_s.result()


def _functional_rows_worker(vectors, values, rows, dps):
    mp.mp.dps = dps
    order = len(values)
    out = []
    for row in rows:
        for column in range(row, order):
            entry = mp.fsum(
                vectors[row][index]
                * values[index]
                * vectors[column][index]
                for index in range(order)
            )
            out.append((row, column, entry))
    return out


def symmetric_functional_calculus(vectors, values):
    order = len(values)
    matrix = mp.zeros(order, order)

    if (
        not PARALLEL
        or available_workers() < 2
        or order < FUNCTIONAL_PARALLEL_MIN_ORDER
    ):
        rows_data = _functional_rows_worker(
            vectors, values, list(range(order)), mp.mp.dps
        )
        for row, column, entry in rows_data:
            matrix[row, column] = entry
            matrix[column, row] = entry
        return matrix

    workers = available_workers(order)
    row_chunks = split_items(list(range(order)), workers)
    dps = mp.mp.dps

    with ProcessPoolExecutor(max_workers=workers) as executor:
        futures = [
            executor.submit(
                _functional_rows_worker, vectors, values, rows, dps
            )
            for rows in row_chunks
        ]
        for future in futures:
            for row, column, entry in future.result():
                matrix[row, column] = entry
                matrix[column, row] = entry

    return matrix


def heights_from_spectrum(scale_value, spectrum):
    nonpositive = [k for k, value in enumerate(spectrum) if value <= 0]
    if nonpositive:
        raise ArithmeticError(
            "nonpositive Jacobi spectrum at indices " + str(nonpositive)
        )
    return [mp.sqrt(scale_value / value) for value in spectrum]


def build_operator(order=ORDER, camera=CAMERA, cutoff=CUTOFF):
    _, _, moments = build_moment_data(order, camera, cutoff)
    scale_value, alpha, beta = recurrence_from_moments(moments, order)
    spectrum, vectors = spectral_data(alpha, beta)
    heights_unsorted = heights_from_spectrum(scale_value, spectrum)
    operator = symmetric_functional_calculus(vectors, heights_unsorted)
    return (
        sorted(heights_unsorted),
        jacobi_matrix(alpha, beta),
        operator,
        spectrum,
        vectors,
        moments,
    )


# ============================================================
# ORDER IDENTITY UTILITIES
# ============================================================

def principal_block(matrix, size):
    out = mp.matrix(size, size)
    for i in range(size):
        for j in range(size):
            out[i, j] = matrix[i, j]
    return out


def max_abs_matrix_difference(a, b):
    maximum = mp.mpf(0)
    for i in range(a.rows):
        for j in range(a.cols):
            maximum = max(maximum, abs(a[i, j] - b[i, j]))
    return maximum


def tridiagonal_defect(matrix):
    maximum = mp.mpf(0)
    for i in range(matrix.rows):
        for j in range(matrix.cols):
            if abs(i - j) > 1:
                maximum = max(maximum, abs(matrix[i, j]))
    return maximum


def jacobi_diagonals(matrix):
    alpha = [matrix[i, i] for i in range(matrix.rows)]
    beta = [matrix[i, i + 1] for i in range(matrix.rows - 1)]
    return alpha, beta


def charpoly_recurrence(alpha, beta, y, size):
    values = [mp.mpf(1)]
    if size == 0:
        return values
    values.append(y - alpha[0])
    for n in range(1, size):
        values.append(
            (y - alpha[n]) * values[n]
            - beta[n - 1] ** 2 * values[n - 1]
        )
    return values


def charpoly_value_and_derivative(alpha, beta, y, size):
    if size == 0:
        return mp.mpf(1), mp.mpf(0)

    p_prev = mp.mpf(1)
    dp_prev = mp.mpf(0)
    p = y - alpha[0]
    dp = mp.mpf(1)

    if size == 1:
        return p, dp

    for n in range(1, size):
        beta_sq = beta[n - 1] ** 2
        p_next = (y - alpha[n]) * p - beta_sq * p_prev
        dp_next = p + (y - alpha[n]) * dp - beta_sq * dp_prev
        p_prev, p = p, p_next
        dp_prev, dp = dp, dp_next

    return p, dp


def relative_residual(lhs, rhs):
    scale_value = max(mp.mpf(1), abs(lhs), abs(rhs))
    return abs(lhs - rhs) / scale_value


def safe_log10_abs(x):
    if x == 0:
        return mp.inf
    return -mp.log10(abs(x))


def asymmetry(matrix):
    return max(
        abs(matrix[row, column] - matrix[column, row])
        for row in range(matrix.rows)
        for column in range(matrix.cols)
    )


# ============================================================
# ANALYTIC ORDER IDENTITY N -> N+1
# ============================================================

def audit_order_identity(order, moments):
    if order < 2:
        raise ValueError("ORDER precisa ser >= 2 para esta auditoria")

    scale_n, alpha_n_rec, beta_n_rec = recurrence_from_moments(moments, order)
    scale_s, alpha_s_rec, beta_s_rec = recurrence_from_moments(moments, order + 1)

    if scale_n != scale_s:
        raise ArithmeticError("N and N+1 unexpectedly received different scaling")
    scale_value = scale_n

    jacobi_n = jacobi_matrix(alpha_n_rec, beta_n_rec)
    jacobi_succ = jacobi_matrix(alpha_s_rec, beta_s_rec)

    (spectrum_n, vectors_n), (spectrum_succ, vectors_succ) = spectral_pair_parallel(
        alpha_n_rec, beta_n_rec, alpha_s_rec, beta_s_rec
    )

    projected = principal_block(jacobi_succ, order)
    projective_defect = max_abs_matrix_difference(jacobi_n, projected)
    tri_defect_n = tridiagonal_defect(jacobi_n)
    tri_defect_succ = tridiagonal_defect(jacobi_succ)

    y_n = spectrum_n[order - 1]
    y_succ = spectrum_succ[order]

    # Heights in the rescaled recurrence satisfy t = sqrt(scale / Y).
    t_n = mp.sqrt(scale_value / y_n)
    t_succ = mp.sqrt(scale_value / y_succ)

    delta_y_actual = y_succ - y_n
    delta_t_actual = t_n - t_succ

    lower_neighbor = spectrum_succ[order - 1]
    interlace_left_gap = y_n - lower_neighbor
    interlace_right_gap = y_succ - y_n

    alpha_succ, beta_succ = jacobi_diagonals(jacobi_succ)
    alpha_n, beta_n = jacobi_diagonals(jacobi_n)

    alpha_boundary = alpha_succ[order]
    beta_boundary = beta_succ[order - 1]
    beta_boundary_sq = beta_boundary ** 2

    char_values = charpoly_recurrence(
        alpha_succ, beta_succ, y_n, order + 1
    )
    p_nm1_at_yn = char_values[order - 1]
    p_n_at_yn = char_values[order]
    p_succ_at_yn = char_values[order + 1]

    recurrence_rhs_full = (
        (y_n - alpha_boundary) * p_n_at_yn
        - beta_boundary_sq * p_nm1_at_yn
    )
    recurrence_rhs_at_root = -beta_boundary_sq * p_nm1_at_yn

    recurrence_residual_full = relative_residual(
        p_succ_at_yn, recurrence_rhs_full
    )
    recurrence_root_residual = relative_residual(
        p_succ_at_yn, recurrence_rhs_at_root
    )

    denominator = mp.fprod(
        y_n - spectrum_succ[j]
        for j in range(order)
    )
    delta_y_formula = (
        beta_boundary_sq * p_nm1_at_yn / denominator
    )
    delta_y_residual = relative_residual(delta_y_actual, delta_y_formula)

    height_denominator = (
        mp.sqrt(y_n * y_succ)
        * (mp.sqrt(y_n) + mp.sqrt(y_succ))
    )
    delta_t_formula = (
        mp.sqrt(scale_value) * delta_y_formula / height_denominator
    )
    delta_t_residual = relative_residual(delta_t_actual, delta_t_formula)

    boundary_visibility_direct = abs(vectors_n[order - 1][order - 1]) ** 2

    p_n_check, dp_n_at_yn = charpoly_value_and_derivative(
        alpha_n, beta_n, y_n, order
    )
    p_nm1_n_at_yn = charpoly_recurrence(
        alpha_n, beta_n, y_n, order - 1
    )[-1]
    boundary_visibility_formula = p_nm1_n_at_yn / dp_n_at_yn
    boundary_visibility_residual = relative_residual(
        boundary_visibility_direct, boundary_visibility_formula
    )

    schur_sum = mp.fsum(
        abs(vectors_n[order - 1][k]) ** 2
        / (y_succ - spectrum_n[k])
        for k in range(order)
    )
    schur_residual_value = (
        y_succ - alpha_boundary - beta_boundary_sq * schur_sum
    )

    schur_rest = mp.fsum(
        abs(vectors_n[order - 1][k]) ** 2
        / (y_succ - spectrum_n[k])
        for k in range(order - 1)
    )
    factorized_left = (
        delta_y_actual
        * (y_succ - alpha_boundary - beta_boundary_sq * schur_rest)
    )
    factorized_right = beta_boundary_sq * boundary_visibility_direct
    factorized_residual = relative_residual(
        factorized_left, factorized_right
    )

    heights_unsorted = heights_from_spectrum(scale_value, spectrum_n)

    return {
        "order": order,
        "scale": scale_value,
        "jacobi_n": jacobi_n,
        "jacobi_succ": jacobi_succ,
        "spectrum_n": spectrum_n,
        "spectrum_succ": spectrum_succ,
        "vectors_n": vectors_n,
        "vectors_succ": vectors_succ,
        "heights_unsorted": heights_unsorted,
        "heights": sorted(heights_unsorted),
        "t_n": t_n,
        "t_succ": t_succ,
        "y_n": y_n,
        "y_succ": y_succ,
        "delta_y_actual": delta_y_actual,
        "delta_y_formula": delta_y_formula,
        "delta_y_residual": delta_y_residual,
        "delta_t_actual": delta_t_actual,
        "delta_t_formula": delta_t_formula,
        "delta_t_residual": delta_t_residual,
        "projective_defect": projective_defect,
        "tri_defect_n": tri_defect_n,
        "tri_defect_succ": tri_defect_succ,
        "lower_neighbor": lower_neighbor,
        "interlace_left_gap": interlace_left_gap,
        "interlace_right_gap": interlace_right_gap,
        "alpha_boundary": alpha_boundary,
        "beta_boundary": beta_boundary,
        "p_nm1_at_yn": p_nm1_at_yn,
        "p_n_at_yn": p_n_at_yn,
        "p_succ_at_yn": p_succ_at_yn,
        "p_n_check": p_n_check,
        "recurrence_residual_full": recurrence_residual_full,
        "recurrence_root_residual": recurrence_root_residual,
        "boundary_visibility_direct": boundary_visibility_direct,
        "boundary_visibility_formula": boundary_visibility_formula,
        "boundary_visibility_residual": boundary_visibility_residual,
        "schur_residual_value": schur_residual_value,
        "factorized_left": factorized_left,
        "factorized_right": factorized_right,
        "factorized_residual": factorized_residual,
    }


def print_order_identity_audit(audit):
    digits = min(ORDER_AUDIT_DIGITS, mp.mp.dps)

    def show(label, value):
        print(f"{label:<42} {mp.nstr(value, digits)}")

    print()
    print("=" * 88)
    print(
        "AUDITORIA ANALITICA DA ORDEM "
        f"N={audit['order']} -> N={audit['order'] + 1}"
    )
    print("=" * 88)

    print("\n[TORRE / BORDO]")
    show("defeito projetivo max", audit["projective_defect"])
    show("defeito tridiagonal J_N", audit["tri_defect_n"])
    show("defeito tridiagonal J_(N+1)", audit["tri_defect_succ"])
    show("alpha_N (novo bordo)", audit["alpha_boundary"])
    show("beta_(N-1) (novo canal)", audit["beta_boundary"])

    print("\n[AUTOVALOR EXTREMO]")
    show("Y_N", audit["y_n"])
    show("Y_(N+1)", audit["y_succ"])
    show("Y_N - vizinho inferior", audit["interlace_left_gap"])
    show("Y_(N+1) - Y_N", audit["interlace_right_gap"])

    print("\n[ALTURA]")
    show("t_N", audit["t_n"])
    show("t_(N+1)", audit["t_succ"])
    show("delta t observado", audit["delta_t_actual"])
    show("delta t pela identidade", audit["delta_t_formula"])
    show("residuo relativo delta t", audit["delta_t_residual"])
    show(
        "casas de separacao t_N/t_(N+1)",
        safe_log10_abs(audit["delta_t_actual"]),
    )

    print("\n[DETERMINANTE / INCREMENTO]")
    show("P_(N-1)(Y_N)", audit["p_nm1_at_yn"])
    show("P_N(Y_N)", audit["p_n_at_yn"])
    show("P_(N+1)(Y_N)", audit["p_succ_at_yn"])
    show("residuo recorrencia completa", audit["recurrence_residual_full"])
    show("residuo recorrencia no polo", audit["recurrence_root_residual"])
    show("delta Y observado", audit["delta_y_actual"])
    show("delta Y pela identidade", audit["delta_y_formula"])
    show("residuo relativo delta Y", audit["delta_y_residual"])

    print("\n[VISIBILIDADE DO BORDO]")
    show("|<e_(N-1),v_N>|^2 direto", audit["boundary_visibility_direct"])
    show("P_(N-1)(Y_N)/P_N'(Y_N)", audit["boundary_visibility_formula"])
    show("residuo relativo visibilidade", audit["boundary_visibility_residual"])

    print("\n[COMPLEMENTO DE SCHUR]")
    show("residuo Schur no novo autovalor", audit["schur_residual_value"])
    show("lado esquerdo fatorado", audit["factorized_left"])
    show("beta^2 * visibilidade", audit["factorized_right"])
    show("residuo relativo fatorado", audit["factorized_residual"])

    print("\n[LEITURA]")
    print(
        "A passagem de ordem e controlada pelo novo canal de bordo "
        "beta_(N-1) e pela massa do modo extremo na ultima coordenada."
    )
    print("Nenhum valor externo de zero/altura foi usado nesta auditoria.")
    print("=" * 88)


# ============================================================
# MAIN
# ============================================================

def main():
    mp.mp.dps = DPS
    workers = available_workers()
    print(
        f"config: camera={CAMERA} cutoff={CUTOFF} order={ORDER} "
        f"dps={DPS} workers={workers} parallel={PARALLEL}"
    )

    total_start = time.perf_counter()

    if TAIL_REFERENCE_AUDIT:
        ref_degree = min(TAIL_REFERENCE_DEGREE, 4 * ORDER)
        fast = exact_tail_series(CAMERA, CUTOFF, ref_degree)
        slow = exact_tail_series_reference(CAMERA, CUTOFF, ref_degree)
        tail_error = max(
            abs(a[0] - b[0]) + abs(a[1] - b[1])
            for a, b in zip(fast, slow)
        )
        print("tail reference max error:", mp.nstr(tail_error, 8))

    if ORDER_IDENTITY_AUDIT:
        t0 = time.perf_counter()
        _, _, moments = build_moment_data(ORDER + 1)
        if PRINT_TIMINGS:
            print(f"moment/germe build: {time.perf_counter() - t0:.3f} s")

        t0 = time.perf_counter()
        audit = audit_order_identity(ORDER, moments)
        if PRINT_TIMINGS:
            print(f"order spectral audit: {time.perf_counter() - t0:.3f} s")

        t0 = time.perf_counter()
        operator = symmetric_functional_calculus(
            audit["vectors_n"], audit["heights_unsorted"]
        )
        if PRINT_TIMINGS:
            print(f"height functional calculus: {time.perf_counter() - t0:.3f} s")

        heights = audit["heights"]
        jacobi = audit["jacobi_n"]

        print("self-adjoint: beta_k > 0 for k = 1 ..", ORDER - 1)
        print("asymmetry of the Jacobi matrix :", mp.nstr(asymmetry(jacobi), 3))
        print("asymmetry of the height operator:", mp.nstr(asymmetry(operator), 3))
        print()
        for value in heights[:COUNT]:
            print(mp.nstr(value, DIGITS))

        print_order_identity_audit(audit)

    else:
        t0 = time.perf_counter()
        heights, jacobi, operator, _, _, _ = build_operator()
        if PRINT_TIMINGS:
            print(f"operator build: {time.perf_counter() - t0:.3f} s")

        print("self-adjoint: beta_k > 0 for k = 1 ..", ORDER - 1)
        print("asymmetry of the Jacobi matrix :", mp.nstr(asymmetry(jacobi), 3))
        print("asymmetry of the height operator:", mp.nstr(asymmetry(operator), 3))
        print()
        for value in heights[:COUNT]:
            print(mp.nstr(value, DIGITS))

    if PRINT_TIMINGS:
        print(f"total: {time.perf_counter() - total_start:.3f} s")


if __name__ == "__main__":
    main()
