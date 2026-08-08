#!/usr/bin/env python3
"""Uniform endpoint-frame bound and all-bases limit audit.

For a fixed finite camera family, endpoint completeness eventually fails: the
integer lcm(b**2) lies at depth at least two in every selected base and is
invisible to all root/first-level endpoint rows.

For the genuinely growing atlas 2 <= b <= N, let

    F_N = sum_b A_b* A_b,
    E_N = F_N**(-1/2) F_boundary,N F_N**(-1/2).

Large bases b>N/2 supply singleton endpoint rows.  For N>=8 this gives

    E_N >= Delta_2 I,
    Delta_2=(sqrt(2)-1)**4/2.

However only b<=sqrt(N) can contain a Green-bulk row.  Consequently the
normalized bulk fraction is O(1/N), and the fixed Poisson completion satisfies

    ||M_MB,N|| = O(N**(-1/2)).

Thus the unweighted growing-all-bases limit is uniformly stable but has a
trivial zero bulk completion.  A nontrivial infinite theory needs a local-
energy/base-renormalized limit rather than uniform counting of all cameras.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any, Sequence

import numpy as np
from scipy.linalg import eigh


def add_row_energy(
    matrix: np.ndarray, indices: Sequence[int], coefficients: Sequence[float]
) -> None:
    index_array = np.asarray(indices, dtype=np.int64)
    coefficient_array = np.asarray(coefficients, dtype=np.float64)
    matrix[np.ix_(index_array, index_array)] += np.outer(
        coefficient_array, coefficient_array
    )


def all_bases_frames(size: int) -> tuple[np.ndarray, np.ndarray]:
    full = np.zeros((size, size), dtype=np.float64)
    endpoint = np.zeros((size, size), dtype=np.float64)
    for base in range(2, size + 1):
        q = base ** -0.5
        for core in range(1, size + 1):
            if core % base == 0:
                continue
            numbers: list[int] = []
            number = core
            while number <= size:
                numbers.append(number - 1)
                number *= base

            add_row_energy(full, (numbers[0],), (1.0 / q,))
            add_row_energy(endpoint, (numbers[0],), (1.0 / q,))
            if len(numbers) == 1:
                continue

            add_row_energy(full, numbers[:2], (-2.0, 1.0 / q))
            add_row_energy(endpoint, numbers[:2], (-2.0, 1.0 / q))
            for depth in range(2, len(numbers)):
                add_row_energy(
                    full,
                    numbers[depth - 2 : depth + 1],
                    (q, -2.0, 1.0 / q),
                )
    return full, endpoint


def fixed_camera_obstruction(bases: Sequence[int]) -> dict[str, Any]:
    witness = 1
    for base in bases:
        witness = math.lcm(witness, base * base)
    depths: dict[str, int] = {}
    for base in bases:
        quotient = witness
        depth = 0
        while quotient % base == 0:
            quotient //= base
            depth += 1
        depths[str(base)] = depth
    return {
        "fixed_bases": list(bases),
        "simultaneous_depth_two_witness": witness,
        "depths_at_witness": depths,
        "endpoint_kernel_statement": (
            "For x=F_N^(1/2)e_witness, the normalized endpoint analysis "
            "annihilates x once the cutoff contains the witness."
        ),
        "conclusion": (
            "No fixed finite base family has a uniform endpoint lower frame "
            "bound on the infinite integers."
        ),
    }


def constants(size: int) -> dict[str, float]:
    maximum_base_factor = (1.0 + 1.0 / math.sqrt(2.0)) ** 4
    high_base_sum = float(sum(range(size // 2 + 1, size + 1)))
    endpoint_diagonal_lower = high_base_sum - float(size)
    full_operator_upper = float(
        sum(
            base * (1.0 + base ** -0.5) ** 4
            for base in range(2, size + 1)
        )
    )
    bulk_operator_upper = float(
        sum(
            base * (1.0 + base ** -0.5) ** 4
            for base in range(2, math.isqrt(size) + 1)
        )
    )
    uniform_delta = 1.0 / (8.0 * maximum_base_factor)
    exact_endpoint_bound = endpoint_diagonal_lower / full_operator_upper
    normalized_bulk_bound = bulk_operator_upper / endpoint_diagonal_lower
    return {
        "K=(1+1/sqrt(2))^4": maximum_base_factor,
        "Delta_2": uniform_delta,
        "endpoint_diagonal_lower": endpoint_diagonal_lower,
        "full_operator_upper": full_operator_upper,
        "bulk_operator_upper": bulk_operator_upper,
        "exact_elementary_endpoint_bound": exact_endpoint_bound,
        "normalized_bulk_upper_bound": normalized_bulk_bound,
    }


def one_size_audit(size: int) -> dict[str, Any]:
    full, endpoint = all_bases_frames(size)
    generalized = eigh(
        endpoint, full, eigvals_only=True, check_finite=False, driver="gvd"
    )
    minimum = float(generalized[0])
    maximum = float(generalized[-1])
    bulk_fraction = 1.0 - minimum
    poisson_norm = math.sqrt(max(0.0, bulk_fraction / minimum))
    bounds = constants(size)
    bulk_upper = bounds["normalized_bulk_upper_bound"]
    theoretical_poisson_upper = (
        math.sqrt(bulk_upper / (1.0 - bulk_upper))
        if bulk_upper < 1.0
        else None
    )
    return {
        "ambient_dimension": size,
        "base_count": size - 1,
        "minimum_generalized_endpoint_eigenvalue": minimum,
        "maximum_generalized_endpoint_eigenvalue": maximum,
        "minimum_endpoint_singular_value": math.sqrt(max(0.0, minimum)),
        "actual_normalized_bulk_operator_norm_squared": bulk_fraction,
        "actual_poisson_completion_norm": poisson_norm,
        "elementary_bounds": bounds,
        "theoretical_poisson_norm_upper_bound": theoretical_poisson_upper,
        "uniform_delta_pass": minimum + 1.0e-12 >= bounds["Delta_2"],
    }


def parse_sizes(text: str) -> tuple[int, ...]:
    values = tuple(int(part.strip()) for part in text.split(",") if part.strip())
    if not values or any(value < 8 for value in values):
        raise ValueError("all sizes must be integers >= 8")
    return values


def run_lab(args: argparse.Namespace) -> dict[str, Any]:
    sizes = parse_sizes(args.sizes)
    fixed_bases = tuple(
        int(part.strip()) for part in args.fixed_bases.split(",") if part.strip()
    )
    if not fixed_bases or any(base < 2 for base in fixed_bases):
        raise ValueError("fixed bases must be integers >=2")
    rows = [one_size_audit(size) for size in sizes]
    delta = (math.sqrt(2.0) - 1.0) ** 4 / 2.0
    return {
        "schema": "org.native-carry.all-bases-uniform-endpoint-bound/v1",
        "status": "FINITE_THEOREM_AUDIT_AND_LIMIT_OBSTRUCTION",
        "fixed_camera_obstruction": fixed_camera_obstruction(fixed_bases),
        "growing_all_bases_theorem": {
            "base_policy": "all positional bases 2 <= b <= N",
            "range": "N>=8",
            "uniform_bound": "E_N* E_N >= Delta_2 I",
            "Delta_2": delta,
            "proof_ingredients": [
                "bases b>N/2 give singleton root rows for every n != b",
                "F_endpoint >= (N^2/8) I",
                "F_full <= K N^2 I with K=(1+1/sqrt(2))^4",
                "1/(8K)=Delta_2",
            ],
        },
        "size_audits": rows,
        "limit_identification": {
            "bulk_support": "only bases b<=sqrt(N) can contain depth>=2 bulk rows",
            "normalized_bulk_bound": "||P_bulk V_N||^2=O(1/N)",
            "poisson_bound": "||M_MB,N||=O(N^(-1/2))",
            "uniform_counting_limit": "M_MB,N -> 0 in operator norm",
            "interpretation": (
                "Uniform counting of all bases proves endpoint stability but "
                "trivializes the Green bulk in the infinite limit."
            ),
            "required_nontrivial_limit": (
                "Use a local-energy or base-renormalized inductive system that "
                "keeps bulk and endpoint contributions comparable."
            ),
        },
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sizes", default="8,16,32,64,128,256")
    parser.add_argument("--fixed-bases", default="2,3,4,5,6,7")
    parser.add_argument("--output", type=Path)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    try:
        report = run_lab(args)
    except ValueError as exc:
        parser.error(str(exc))
    payload = json.dumps(report, indent=2, sort_keys=True)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload + "\n", encoding="utf-8")
    print(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
