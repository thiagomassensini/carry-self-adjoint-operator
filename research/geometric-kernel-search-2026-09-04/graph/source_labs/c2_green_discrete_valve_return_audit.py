#!/usr/bin/env python3
"""Exact audit of the discrete-valve return in the native C2 Green chart.

The audit is genuine-first and self-contained. It proves the finite algebraic
factorization in the FULL-EVEN cross-Lagrangian coordinates, checks the local
Green form, separates the uniformly bounded endpoint functional from the
unbounded full cumulative return, and preserves the exact J/H coequalizer
kernel obstruction at the current arithmetic endpoint frontier.

All finite algebra is performed exactly in Q(sqrt(2)) or Q(sqrt(3)); no CAS,
solver, fitted endpoint, external completion, or spectral data is used.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import json
import math
from typing import Sequence


@dataclass(frozen=True, eq=False)
class Quadratic:
    """A tiny exact implementation of a+b*sqrt(d)."""

    d: int
    rational: Fraction
    radical: Fraction

    def __init__(
        self,
        d: int,
        rational: int | Fraction = 0,
        radical: int | Fraction = 0,
    ) -> None:
        if d <= 0:
            raise ValueError("d must be positive")
        object.__setattr__(self, "d", d)
        object.__setattr__(self, "rational", Fraction(rational))
        object.__setattr__(self, "radical", Fraction(radical))

    def _coerce(self, other: object) -> "Quadratic":
        if isinstance(other, Quadratic):
            if other.d != self.d:
                raise TypeError("cannot mix different quadratic fields")
            return other
        if isinstance(other, (int, Fraction)):
            return Quadratic(self.d, other)
        return NotImplemented  # type: ignore[return-value]

    def __add__(self, other: object) -> "Quadratic":
        value = self._coerce(other)
        if value is NotImplemented:
            return NotImplemented
        return Quadratic(
            self.d,
            self.rational + value.rational,
            self.radical + value.radical,
        )

    __radd__ = __add__

    def __neg__(self) -> "Quadratic":
        return Quadratic(self.d, -self.rational, -self.radical)

    def __sub__(self, other: object) -> "Quadratic":
        value = self._coerce(other)
        if value is NotImplemented:
            return NotImplemented
        return self + (-value)

    def __rsub__(self, other: object) -> "Quadratic":
        value = self._coerce(other)
        if value is NotImplemented:
            return NotImplemented
        return value - self

    def __mul__(self, other: object) -> "Quadratic":
        value = self._coerce(other)
        if value is NotImplemented:
            return NotImplemented
        return Quadratic(
            self.d,
            self.rational * value.rational
            + self.d * self.radical * value.radical,
            self.rational * value.radical + self.radical * value.rational,
        )

    __rmul__ = __mul__

    def inverse(self) -> "Quadratic":
        denominator = self.rational**2 - self.d * self.radical**2
        if denominator == 0:
            raise ZeroDivisionError("zero quadratic element")
        return Quadratic(
            self.d,
            self.rational / denominator,
            -self.radical / denominator,
        )

    def __truediv__(self, other: object) -> "Quadratic":
        value = self._coerce(other)
        if value is NotImplemented:
            return NotImplemented
        return self * value.inverse()

    def __rtruediv__(self, other: object) -> "Quadratic":
        value = self._coerce(other)
        if value is NotImplemented:
            return NotImplemented
        return value / self

    def __eq__(self, other: object) -> bool:
        value = self._coerce(other)
        if value is NotImplemented:
            return False
        return self.rational == value.rational and self.radical == value.radical

    def __bool__(self) -> bool:
        return self.rational != 0 or self.radical != 0

    def __str__(self) -> str:
        a, b = self.rational, self.radical
        if b == 0:
            return str(a)
        radical = f"sqrt({self.d})"
        if b == 1:
            b_text = radical
        elif b == -1:
            b_text = f"-{radical}"
        else:
            b_text = f"{b}*{radical}"
        if a == 0:
            return b_text
        sign = "+" if b > 0 else "-"
        unsigned = radical if abs(b) == 1 else f"{abs(b)}*{radical}"
        return f"{a}{sign}{unsigned}"


def q2(rational: int | Fraction = 0, radical: int | Fraction = 0) -> Quadratic:
    return Quadratic(2, rational, radical)


def q3(rational: int | Fraction = 0, radical: int | Fraction = 0) -> Quadratic:
    return Quadratic(3, rational, radical)


Matrix = list[list[Quadratic]]


def zero_matrix(rows: int, columns: int, d: int = 2) -> Matrix:
    return [[Quadratic(d) for _ in range(columns)] for _ in range(rows)]


def identity_matrix(size: int, d: int = 2) -> Matrix:
    matrix = zero_matrix(size, size, d)
    for index in range(size):
        matrix[index][index] = Quadratic(d, 1)
    return matrix


def matrix_shape(matrix: Matrix) -> tuple[int, int]:
    return len(matrix), len(matrix[0]) if matrix else 0


def matrix_add(left: Matrix, right: Matrix) -> Matrix:
    if matrix_shape(left) != matrix_shape(right):
        raise ValueError("matrix shape mismatch")
    return [
        [left[i][j] + right[i][j] for j in range(len(left[0]))]
        for i in range(len(left))
    ]


def matrix_sub(left: Matrix, right: Matrix) -> Matrix:
    if matrix_shape(left) != matrix_shape(right):
        raise ValueError("matrix shape mismatch")
    return [
        [left[i][j] - right[i][j] for j in range(len(left[0]))]
        for i in range(len(left))
    ]


def matrix_mul(left: Matrix, right: Matrix) -> Matrix:
    left_rows, left_columns = matrix_shape(left)
    right_rows, right_columns = matrix_shape(right)
    if left_columns != right_rows:
        raise ValueError("matrix multiplication shape mismatch")
    d = left[0][0].d if left_rows and left_columns else right[0][0].d
    output = zero_matrix(left_rows, right_columns, d)
    for i in range(left_rows):
        for k in range(left_columns):
            if not left[i][k]:
                continue
            for j in range(right_columns):
                output[i][j] = output[i][j] + left[i][k] * right[k][j]
    return output


def transpose(matrix: Matrix) -> Matrix:
    rows, columns = matrix_shape(matrix)
    return [[matrix[i][j] for i in range(rows)] for j in range(columns)]


def vstack(top: Matrix, bottom: Matrix) -> Matrix:
    if matrix_shape(top)[1] != matrix_shape(bottom)[1]:
        raise ValueError("vstack shape mismatch")
    return [*top, *bottom]


def hstack(left: Matrix, right: Matrix) -> Matrix:
    if matrix_shape(left)[0] != matrix_shape(right)[0]:
        raise ValueError("hstack shape mismatch")
    return [left[i] + right[i] for i in range(len(left))]


def block_diagonal(blocks: Sequence[Matrix]) -> Matrix:
    row_count = sum(matrix_shape(block)[0] for block in blocks)
    column_count = sum(matrix_shape(block)[1] for block in blocks)
    output = zero_matrix(row_count, column_count)
    row_offset = 0
    column_offset = 0
    for block in blocks:
        rows, columns = matrix_shape(block)
        for i in range(rows):
            for j in range(columns):
                output[row_offset + i][column_offset + j] = block[i][j]
        row_offset += rows
        column_offset += columns
    return output


def matrix_rank(matrix: Matrix) -> int:
    work = [row[:] for row in matrix]
    rows, columns = matrix_shape(work)
    pivot_row = 0
    for column in range(columns):
        pivot = next((row for row in range(pivot_row, rows) if work[row][column]), None)
        if pivot is None:
            continue
        work[pivot_row], work[pivot] = work[pivot], work[pivot_row]
        inverse = work[pivot_row][column].inverse()
        work[pivot_row] = [entry * inverse for entry in work[pivot_row]]
        for row in range(rows):
            if row == pivot_row or not work[row][column]:
                continue
            coefficient = work[row][column]
            work[row] = [
                work[row][j] - coefficient * work[pivot_row][j]
                for j in range(columns)
            ]
        pivot_row += 1
        if pivot_row == rows:
            break
    return pivot_row


def outer(left: Sequence[Quadratic], right: Sequence[Quadratic]) -> Matrix:
    return [[a * b for b in right] for a in left]


def skew_outer(left: Sequence[Quadratic], right: Sequence[Quadratic]) -> Matrix:
    return matrix_sub(outer(left, right), outer(right, left))


def v2(value: int) -> int:
    if value <= 0:
        raise ValueError("v2 is defined only on positive integers")
    exponent = 0
    while value % 2 == 0:
        value //= 2
        exponent += 1
    return exponent


def native_weight(cell: int) -> Fraction:
    if cell < 1:
        raise ValueError("cell index must be positive")
    return Fraction(1, 1 << v2(2 * cell))


def edge_incidence_matrix(cell_count: int) -> Matrix:
    if cell_count < 1:
        raise ValueError("cell_count must be positive")
    edge_count = 2 * cell_count
    matrix = zero_matrix(edge_count, edge_count + 1)
    for edge in range(edge_count):
        matrix[edge][edge] = q2(-1)
        matrix[edge][edge + 1] = q2(1)
    return matrix


def local_cross_analysis(weight: Fraction) -> Matrix:
    """(x_left,x_right) -> (o,p), exactly in Q(sqrt(2))."""

    return [
        [q2(0, Fraction(-1, 2)), q2(0, Fraction(-1, 2))],
        [q2(0, -weight / 2), q2(0, weight / 2)],
    ]


def local_cross_reconstruction(weight: Fraction) -> Matrix:
    """Exact inverse (o,p) -> (x_left,x_right)."""

    return [
        [q2(0, Fraction(-1, 2)), q2(0, -Fraction(1, 2) / weight)],
        [q2(0, Fraction(-1, 2)), q2(0, Fraction(1, 2) / weight)],
    ]


def cross_analysis_matrix(cell_count: int) -> Matrix:
    return block_diagonal(
        [local_cross_analysis(native_weight(j)) for j in range(1, cell_count + 1)]
    )


def cross_reconstruction_matrix(cell_count: int) -> Matrix:
    return block_diagonal(
        [
            local_cross_reconstruction(native_weight(j))
            for j in range(1, cell_count + 1)
        ]
    )


def bulk_matrix(cell_count: int) -> Matrix:
    """B_C2 f=(p_j): the weighted even-center curvature."""

    vertex_count = 2 * cell_count + 1
    matrix = zero_matrix(cell_count, vertex_count)
    for j in range(1, cell_count + 1):
        weight = native_weight(j)
        left, center, right = 2 * j - 2, 2 * j - 1, 2 * j
        matrix[j - 1][left] = q2(0, weight / 2)
        matrix[j - 1][center] = q2(0, -weight)
        matrix[j - 1][right] = q2(0, weight / 2)
    return matrix


def trace_matrix(cell_count: int) -> Matrix:
    """Tr_C2 f=(a,o_1,...,o_J), a=f_1, o=(f_L-f_R)/sqrt(2)."""

    vertex_count = 2 * cell_count + 1
    matrix = zero_matrix(cell_count + 1, vertex_count)
    matrix[0][0] = q2(1)
    for j in range(1, cell_count + 1):
        left, right = 2 * j - 2, 2 * j
        matrix[j][left] = q2(0, Fraction(1, 2))
        matrix[j][right] = q2(0, Fraction(-1, 2))
    return matrix


def green_matrix(cell_count: int) -> Matrix:
    """Green lift of p with zero valve trace."""

    matrix = zero_matrix(2 * cell_count + 1, cell_count)
    for j in range(1, cell_count + 1):
        center = 2 * j - 1
        matrix[center][j - 1] = q2(0, -Fraction(1, 2) / native_weight(j))
    return matrix


def return_matrix(cell_count: int) -> Matrix:
    """Return lift of (a,o) with zero weighted curvature p."""

    vertex_count = 2 * cell_count + 1
    matrix = zero_matrix(vertex_count, cell_count + 1)
    for vertex in range(vertex_count):
        matrix[vertex][0] = q2(1)
    for j in range(1, cell_count + 1):
        center_vertex = 2 * j
        right_vertex = 2 * j + 1
        for vertex_zero_based in range(vertex_count):
            vertex = vertex_zero_based + 1
            if vertex == center_vertex:
                matrix[vertex_zero_based][j] = q2(0, Fraction(-1, 2))
            elif vertex >= right_vertex:
                matrix[vertex_zero_based][j] = q2(0, -1)
    return matrix


def finite_valve_audit(cell_count: int) -> dict[str, object]:
    """Prove I=G B+R Tr and all splitting identities exactly."""

    bulk = bulk_matrix(cell_count)
    trace = trace_matrix(cell_count)
    green = green_matrix(cell_count)
    returned = return_matrix(cell_count)
    vertex_count = 2 * cell_count + 1
    valve = vstack(bulk, trace)
    inverse = hstack(green, returned)

    flags = {
        "identity_factorization": matrix_add(
            matrix_mul(green, bulk), matrix_mul(returned, trace)
        )
        == identity_matrix(vertex_count),
        "bulk_green_identity": matrix_mul(bulk, green) == identity_matrix(cell_count),
        "trace_return_identity": matrix_mul(trace, returned)
        == identity_matrix(cell_count + 1),
        "trace_green_zero": matrix_mul(trace, green)
        == zero_matrix(cell_count + 1, cell_count),
        "bulk_return_zero": matrix_mul(bulk, returned)
        == zero_matrix(cell_count, cell_count + 1),
        "two_sided_coordinate_inverse": matrix_mul(valve, inverse)
        == identity_matrix(vertex_count)
        and matrix_mul(inverse, valve) == identity_matrix(vertex_count),
    }
    if not all(flags.values()):
        raise RuntimeError(f"finite C2 valve failed at J={cell_count}: {flags}")

    incidence = edge_incidence_matrix(cell_count)
    reconstructed = matrix_mul(
        cross_reconstruction_matrix(cell_count),
        matrix_mul(cross_analysis_matrix(cell_count), incidence),
    )
    if reconstructed != incidence:
        raise RuntimeError("cross-Lagrangian edge reconstruction failed")

    endpoint_from_trace = zero_matrix(1, cell_count + 1)
    endpoint_from_trace[0][0] = q2(1)
    for j in range(1, cell_count + 1):
        endpoint_from_trace[0][j] = q2(0, -1)
    endpoint_row = zero_matrix(1, vertex_count)
    endpoint_row[0][-1] = q2(1)
    endpoint_residual = matrix_sub(endpoint_row, matrix_mul(endpoint_from_trace, trace))
    if endpoint_residual != zero_matrix(1, vertex_count):
        raise RuntimeError("moving endpoint formula failed")

    rank = matrix_rank(bulk)
    return {
        "J": cell_count,
        "vertex_dimension": vertex_count,
        "bulk_rank": rank,
        "bulk_kernel_dimension": vertex_count - rank,
        "trace_rank_on_bulk_kernel_required": vertex_count - rank,
        "flags": flags,
        "edge_reconstruction_residual_zero": True,
        "endpoint_formula": "f_(2J+1)=a-sqrt(2) sum_(j<=J)o_j",
        "endpoint_residual_zero": True,
    }


def local_green_audit() -> dict[str, object]:
    """Verify the native boundary Green form at weight one.

    Every term is homogeneous of degree one in omega, so the exact weight-one
    matrix identity proves it for every nonzero cell weight.
    """

    gamma0 = [
        [q2(1), q2(), q2()],
        [q2(), q2(), q2(1)],
    ]
    gamma1 = [
        [q2(1), q2(-1), q2()],
        [q2(), q2(-1), q2(1)],
    ]
    boundary = matrix_sub(
        matrix_mul(transpose(gamma0), gamma1),
        matrix_mul(transpose(gamma1), gamma0),
    )

    u = [q2(0, Fraction(1, 2)), q2(), q2(0, Fraction(1, 2))]
    o = [q2(0, Fraction(1, 2)), q2(), q2(0, Fraction(-1, 2))]
    p = [q2(0, Fraction(1, 2)), q2(0, -1), q2(0, Fraction(1, 2))]
    q_h = o[:]
    active = skew_outer(u, p)
    haar = matrix_add(active, skew_outer(o, q_h))
    laplacian_center = [q2(-1), q2(2), q2(-1)]
    center_value = [q2(), q2(1), q2()]
    interior = skew_outer(laplacian_center, center_value)

    flags = {
        "boundary_to_haar": boundary == haar,
        "odd_channel_cancellation": haar == active,
        "boundary_to_interior": boundary == interior,
        "q_equals_omega_o": q_h == o,
    }
    if not all(flags.values()):
        raise RuntimeError(f"local Green identity failed: {flags}")
    return {
        "boundary_form": "<Gamma0 f,Gamma1 g>-<Gamma1 f,Gamma0 g>",
        "haar_form": "u_f p_g-p_f u_g",
        "interior_form": "(Delta_C2 f)_C g_C-f_C(Delta_C2 g)_C",
        "homogeneous_in_omega": True,
        "flags": flags,
        "checkpoint": "PASS_TFVD_C2_LOCAL_GREEN_WEDGE",
    }


def hardy_weight(edge: int) -> float:
    if edge < 1:
        raise ValueError("edge index must be positive")
    return edge * (1.0 + math.log(edge)) ** 2


def endpoint_and_return_topology_audit() -> dict[str, object]:
    """Separate the bounded endpoint trace from the full cumulative return."""

    partials = []
    running = 0.0
    requested = {1, 2, 4, 8, 16, 64, 256, 1024, 4096, 16384}
    for edge in range(1, max(requested) + 1):
        running += 1.0 / hardy_weight(edge)
        if edge in requested:
            partials.append({"N": edge, "sum_inverse_h": running})
    if running >= 2.0:
        raise RuntimeError("elementary endpoint dual bound was violated")

    lower_bounds = []
    for start in (4, 8, 16, 32, 64, 128, 256, 512):
        stop = start * start
        mass = sum(1.0 / hardy_weight(edge) for edge in range(start, stop + 1))
        input_norm_squared = mass + mass * mass
        plateau_norm_squared = start * mass * mass
        ratio_lower_bound = math.sqrt(plateau_norm_squared / input_norm_squared)
        lower_bounds.append(
            {
                "start": start,
                "stop": stop,
                "edge_energy": mass,
                "seed_squared": mass * mass,
                "vertex_l2_norm_squared_lower_bound": plateau_norm_squared,
                "operator_ratio_lower_bound": ratio_lower_bound,
            }
        )
    if lower_bounds[-1]["operator_ratio_lower_bound"] <= lower_bounds[0][
        "operator_ratio_lower_bound"
    ]:
        raise RuntimeError("cumulative-return lower bound did not grow")

    return {
        "endpoint_dual_partial_sums": partials,
        "endpoint_uniform_bound": "sum_n 1/[n(1+log n)^2] <= 2",
        "endpoint_functional_bounded": True,
        "cumulative_return_l2_lower_bounds": lower_bounds,
        "cumulative_return_uniformly_bounded_into_vertex_l2": False,
        "interpretation": (
            "the outer boundary value is continuous on the weighted edge energy, "
            "while reconstruction of the whole vertex sequence is a closed/unbounded "
            "return unless the target graph norm is strengthened"
        ),
    }


def coequalizer_gate_audit() -> dict[str, object]:
    """Preserve the latest exact obstruction to the arithmetic endpoint lift."""

    quotient_gauge = Fraction(1) - Fraction(1)
    analysis_value = q3(Fraction(1, 2), Fraction(-1, 2))
    if quotient_gauge != 0:
        raise RuntimeError("the frozen J/H gauge is not in ker Q")
    if not analysis_value:
        raise RuntimeError("the frozen A-side kernel witness disappeared")
    return {
        "Q": [[1, 1]],
        "gauge": [1, -1],
        "Q_gauge": [quotient_gauge],
        "A_even_pre": ["1/2", "sqrt(3)/2"],
        "A_even_pre_gauge": analysis_value,
        "nonzero_proof": "(1-sqrt(3))/2 != 0 because 1^2 != 3",
        "kernel_inclusion": False,
        "A_descends_through_Q": False,
        "checkpoint": "STOP_NATIVE_A_NONZERO_ON_COEQUALIZER_KERNEL",
        "frontier": "NEEDS_PROVENANCE_ENRICHED_VALVE_GRAPH_RELATION",
        "why_tfvd_does_not_erase_it": (
            "the C2 valve is an invertible change of coordinates before Q; "
            "an invertible return cannot turn a nonzero A-value on ker Q into zero"
        ),
    }


def build_audit(maximum_cells: int = 8) -> dict[str, object]:
    finite = [finite_valve_audit(j) for j in range(1, maximum_cells + 1)]
    green = local_green_audit()
    topology = endpoint_and_return_topology_audit()
    gate = coequalizer_gate_audit()
    return {
        "schema": "c2.green.tfvd_return_audit.v1",
        "regime": "GENUINE FIRST",
        "decision": (
            "PASS finite/native geometric boundary return; "
            "STOP arithmetic A descent through the current J/H quotient"
        ),
        "passes": [
            "PASS_TFVD_C2_FINITE_VALVE_FACTORIZATION",
            "PASS_TFVD_C2_EDGE_PAIR_RETURN",
            "PASS_TFVD_C2_MOVING_ENDPOINT_LEDGER",
            green["checkpoint"],
            "PASS_TFVD_C2_ENDPOINT_TRACE_UNIFORMLY_BOUNDED",
        ],
        "qualified_stops": [
            "STOP_FIXED_FINITE_TRACE_FOR_P_ONLY_BULK",
            "STOP_FULL_CUMULATIVE_RETURN_UNBOUNDED_IN_VERTEX_L2",
            gate["checkpoint"],
        ],
        "finite_valve": finite,
        "green_identity": green,
        "return_topology": topology,
        "arithmetic_gate": gate,
        "dimension_statement": (
            "for J cells, rank(B_C2)=J and dim ker(B_C2)=J+1; "
            "a p-only valve therefore needs J+1 independent trace coordinates. "
            "A cutoff-independent two-scalar trace requires the full second difference "
            "or an equivalent bracket-plus-carry bulk completion."
        ),
        "next_object": (
            "an enriched graph relation that keeps the A-side indices "
            "(p_A,tau,d_J,cell,corner,orientation,flags,role) before Q, "
            "while quotienting only the tower value/flux side"
        ),
        "full_native_endpoint_graph_lift_constructed": False,
        "analysis_value_divisibility_proved": False,
        "Green_to_zero_claimed": False,
        "external_completion_used": False,
        "solver_used": False,
    }


def json_default(value: object) -> object:
    if isinstance(value, Fraction):
        return {
            "numerator": value.numerator,
            "denominator": value.denominator,
            "text": str(value),
        }
    if isinstance(value, Quadratic):
        return str(value)
    raise TypeError(f"cannot encode {type(value).__name__}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--maximum-cells", type=int, default=8)
    args = parser.parse_args(argv)
    if args.maximum_cells < 1:
        parser.error("--maximum-cells must be positive")
    print(
        json.dumps(
            build_audit(args.maximum_cells),
            indent=2,
            sort_keys=True,
            allow_nan=False,
            default=json_default,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

