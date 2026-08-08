#!/usr/bin/env python3
"""Compact executable demo of the carry self-adjoint port operator.

This program does not define a new native carry operator.  It assembles, in one
place, objects already implemented by the Pythagorean node-return laboratories:

    T_raw                    total carry analysis before whitening
    V = T_raw (T_raw* T_raw)^(-1/2) = (E, B)^T
    L e_n = log(n) e_n
    H = V L V*               on ran(V), and zero on ker(V*)
    M_MB = B E^dagger

The demo verifies numerically that

    V*V = I,
    H* = H,
    H V = V L,
    exp(-itH) V alpha = V exp(-itL) alpha,
    E*E + B*B = I,
    M_MB E = B,
    (Q_E + Q_B M_MB) E = C_native.

The capital T in the polar normalization is an analysis operator.  It is not
the angular height t, and it is not the Green trace Tr_q.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any, Sequence

import numpy as np
from scipy.sparse.linalg import expm_multiply

import native_carry_collective_operator_lab as collective
import native_carry_primitive_real_operator_all_bases_fixed as native
import native_carry_pythagorean_node_weyl_colligation_lab as node_weyl


def parse_times(text: str) -> tuple[float, ...]:
    values = tuple(float(part.strip()) for part in text.split(",") if part.strip())
    if not values or any(not math.isfinite(value) for value in values):
        raise ValueError("provide one or more finite times separated by commas")
    return values


def operator_norm(matrix: np.ndarray) -> float:
    """Spectral norm, with the exact zero case handled cheaply."""
    if matrix.size == 0 or not np.any(matrix):
        return 0.0
    return float(np.linalg.norm(matrix, ord=2))


def complex_pair(value: complex) -> list[float]:
    return [float(value.real), float(value.imag)]


def cancellation_cosine(left: np.ndarray, right: np.ndarray) -> float | None:
    denominator = float(np.linalg.norm(left) * np.linalg.norm(right))
    if denominator == 0.0:
        return None
    return float(np.vdot(left, right).real / denominator)


def build_demo(
    cameras: Sequence[int], cutoff: int, times: Sequence[float], spectrum: bool
) -> dict[str, Any]:
    models = [native.build_camera_model(camera, cutoff) for camera in cameras]
    camera_matrix, size = collective.native_readout_matrix(models)

    # The existing laboratory constructs the carry-weighted raw frame,
    # whitens it, and returns the normalized endpoint/bulk colligation.
    colligation = node_weyl.normalized_colligation(size)
    endpoint = np.asarray(colligation["endpoint"], dtype=np.float64)
    bulk = np.asarray(colligation["bulk"], dtype=np.float64)
    poisson = np.asarray(colligation["poisson"], dtype=np.float64)

    # V is an isometry from integer states into the full port space.
    analysis = np.vstack((endpoint, bulk))
    state_dimension = analysis.shape[1]
    port_dimension = analysis.shape[0]
    endpoint_dimension = endpoint.shape[0]
    bulk_dimension = bulk.shape[0]

    logarithms = np.log(np.arange(1, state_dimension + 1, dtype=np.float64))

    # H = V L V*.  Since V*V=I, H is L on ran(V) and zero on ker(V*).
    generator = (analysis * logarithms[None, :]) @ analysis.T
    coherent_projection = analysis @ analysis.T
    identity_state = np.eye(state_dimension, dtype=np.float64)
    identity_port = np.eye(port_dimension, dtype=np.float64)

    isometry_error = operator_norm(analysis.T @ analysis - identity_state)
    projection_error = operator_norm(
        coherent_projection @ coherent_projection - coherent_projection
    )
    self_adjoint_error = operator_norm(generator - generator.T)
    intertwining_error = operator_norm(
        generator @ analysis - analysis * logarithms[None, :]
    )
    gauge_generator_error = operator_norm(generator @ (identity_port - coherent_projection))

    endpoint_bulk_ledger_error = operator_norm(
        endpoint.T @ endpoint + bulk.T @ bulk - identity_state
    )
    poisson_error = operator_norm(poisson @ endpoint - bulk)

    # The native readout is transported to the port space and then reduced to
    # endpoint data without discarding the bulk.
    full_readout = camera_matrix @ analysis.T
    endpoint_readout = full_readout[:, :endpoint_dimension]
    bulk_readout = full_readout[:, endpoint_dimension:]
    effective_readout = endpoint_readout + bulk_readout @ poisson
    effective_readout_error = operator_norm(effective_readout @ endpoint - camera_matrix)

    spectrum_audit: dict[str, Any]
    if spectrum:
        eigenvalues = np.linalg.eigvalsh(generator)
        expected = np.sort(
            np.concatenate(
                (
                    np.zeros(port_dimension - state_dimension, dtype=np.float64),
                    logarithms,
                )
            )
        )
        spectrum_audit = {
            "computed": True,
            "zero_gauge_multiplicity_expected": port_dimension - state_dimension,
            "zero_eigenvalue_total_expected_including_log_1": (
                port_dimension - state_dimension + 1
            ),
            "maximum_spectrum_error_against_zero_plus_log_n": float(
                np.max(np.abs(eigenvalues - expected))
            ),
            "smallest_eigenvalues": eigenvalues[: min(8, eigenvalues.size)].tolist(),
            "largest_eigenvalues": eigenvalues[-min(8, eigenvalues.size) :].tolist(),
        }
    else:
        spectrum_audit = {"computed": False}

    numbers = np.arange(1, state_dimension + 1, dtype=np.float64)
    alpha = numbers ** -0.5
    initial_port_state = analysis @ alpha.astype(np.complex128)
    initial_mass = float(np.vdot(alpha, alpha).real)

    orbit_rows: list[dict[str, Any]] = []
    for time_value in times:
        native_state = alpha * np.exp(-1j * time_value * logarithms)
        exact_port_state = analysis @ native_state

        # Independent evolution using the full port generator H.
        evolved_port_state = expm_multiply(
            (-1j * time_value) * generator, initial_port_state
        )

        endpoint_state = endpoint @ native_state
        bulk_state = bulk @ native_state
        endpoint_energy = float(np.vdot(endpoint_state, endpoint_state).real)
        bulk_energy = float(np.vdot(bulk_state, bulk_state).real)
        port_energy = float(np.vdot(exact_port_state, exact_port_state).real)

        direct_characteristic = camera_matrix @ native_state
        endpoint_contribution = endpoint_readout @ endpoint_state
        bulk_contribution = bulk_readout @ bulk_state
        completed_characteristic = endpoint_contribution + bulk_contribution
        endpoint_only_effective = effective_readout @ endpoint_state

        orbit_rows.append(
            {
                "time": float(time_value),
                "native_state_mass": float(np.vdot(native_state, native_state).real),
                "port_state_mass": port_energy,
                "endpoint_energy": endpoint_energy,
                "bulk_energy": bulk_energy,
                "pythagorean_energy_error": abs(
                    port_energy - endpoint_energy - bulk_energy
                ),
                "port_vs_native_mass_error": abs(port_energy - initial_mass),
                "H_evolution_vs_log_orbit_error": float(
                    np.linalg.norm(evolved_port_state - exact_port_state)
                ),
                "poisson_state_error": float(
                    np.linalg.norm(poisson @ endpoint_state - bulk_state)
                ),
                "native_characteristic_norm": float(
                    np.linalg.norm(direct_characteristic)
                ),
                "endpoint_contribution_norm": float(
                    np.linalg.norm(endpoint_contribution)
                ),
                "bulk_contribution_norm": float(np.linalg.norm(bulk_contribution)),
                "endpoint_bulk_cancellation_cosine": cancellation_cosine(
                    endpoint_contribution, bulk_contribution
                ),
                "split_characteristic_error": float(
                    np.linalg.norm(completed_characteristic - direct_characteristic)
                ),
                "effective_endpoint_characteristic_error": float(
                    np.linalg.norm(endpoint_only_effective - direct_characteristic)
                ),
                "characteristic": [
                    complex_pair(complex(value)) for value in direct_characteristic
                ],
            }
        )

    return {
        "schema": "org.native-carry.selfadjoint-port-operator-demo/v1",
        "status": "SELFADJOINT_CARRY_PORT_OPERATOR_EXECUTED",
        "configuration": {
            "cameras": list(cameras),
            "native_cutoff": cutoff,
            "times": list(times),
        },
        "notation": {
            "T_capital": "total carry analysis before quadratic whitening",
            "t_lowercase": "real angular evolution parameter",
            "Tr_q": "local weighted Green trace; a different object",
            "V": "normalized isometric analysis T(T*T)^(-1/2)",
            "H": "transported self-adjoint generator V diag(log n) V* plus zero gauge",
        },
        "dimensions": {
            "integer_state": state_dimension,
            "full_port_space": port_dimension,
            "endpoint_ports": endpoint_dimension,
            "bulk_ports": bulk_dimension,
            "gauge_dimension": port_dimension - state_dimension,
        },
        "static_operator_audit": {
            "V_star_V_minus_I_norm": isometry_error,
            "VV_star_projection_error": projection_error,
            "H_minus_H_star_norm": self_adjoint_error,
            "H_V_minus_V_L_norm": intertwining_error,
            "H_on_gauge_norm": gauge_generator_error,
            "E_star_E_plus_B_star_B_minus_I_norm": endpoint_bulk_ledger_error,
            "M_MB_E_minus_B_norm": poisson_error,
            "Q_eff_E_minus_C_native_norm": effective_readout_error,
            "poisson_operator_norm": float(np.linalg.norm(poisson, ord=2)),
            "endpoint_minimum_eigenvalue": float(
                np.linalg.eigvalsh(endpoint.T @ endpoint)[0]
            ),
            "bulk_operator_norm_squared": float(
                np.linalg.eigvalsh(bulk.T @ bulk)[-1]
            ),
        },
        "spectrum_audit": spectrum_audit,
        "orbit_audit": orbit_rows,
        "interpretation": {
            "self_adjointness": (
                "H is self-adjoint because L=diag(log n) is self-adjoint and V "
                "is an isometry; endpoint/bulk orthogonality alone is not the proof."
            ),
            "time_independence": (
                "T, V, E, B, M_MB and H are built before t.  Time only evolves "
                "the already fixed state through exp(-itH)."
            ),
            "bulk": (
                "B collects the normalized depth-at-least-two Green ports from "
                "the vertical towers of all bases."
            ),
            "readout": (
                "Endpoint and bulk are orthogonal port sectors, but their images "
                "under the same camera readout can interfere and cancel."
            ),
        },
    }


def print_summary(report: dict[str, Any]) -> None:
    dims = report["dimensions"]
    audit = report["static_operator_audit"]
    print("=" * 88)
    print(" NATIVE CARRY SELF-ADJOINT PORT OPERATOR DEMO")
    print("=" * 88)
    print(
        "dimensions: "
        f"state={dims['integer_state']}  ports={dims['full_port_space']}  "
        f"endpoint={dims['endpoint_ports']}  bulk={dims['bulk_ports']}  "
        f"gauge={dims['gauge_dimension']}"
    )
    print(f"||V*V-I||                      = {audit['V_star_V_minus_I_norm']:.3e}")
    print(f"||H-H*||                       = {audit['H_minus_H_star_norm']:.3e}")
    print(f"||HV-VL||                      = {audit['H_V_minus_V_L_norm']:.3e}")
    print(f"||H|gauge||                    = {audit['H_on_gauge_norm']:.3e}")
    print(
        f"||E*E+B*B-I||                 = "
        f"{audit['E_star_E_plus_B_star_B_minus_I_norm']:.3e}"
    )
    print(f"||M_MB E-B||                   = {audit['M_MB_E_minus_B_norm']:.3e}")
    print(f"||Q_eff E-C_native||           = {audit['Q_eff_E_minus_C_native_norm']:.3e}")
    print(f"lambda_min(E*E)                = {audit['endpoint_minimum_eigenvalue']:.12f}")
    print(f"||B||^2                        = {audit['bulk_operator_norm_squared']:.12f}")
    print(f"||M_MB||                       = {audit['poisson_operator_norm']:.12f}")
    spectrum = report["spectrum_audit"]
    if spectrum.get("computed"):
        print(
            "spectrum error vs {0 gauge} union {log n} = "
            f"{spectrum['maximum_spectrum_error_against_zero_plus_log_n']:.3e}"
        )
    print("-" * 88)
    print(
        "       t        mass error       H-orbit error      Poisson error       "
        "|C psi_t|      endpoint/bulk cosine"
    )
    for row in report["orbit_audit"]:
        cosine = row["endpoint_bulk_cancellation_cosine"]
        cosine_text = "n/a" if cosine is None else f"{cosine: .6f}"
        print(
            f"{row['time']:10.6f}  "
            f"{row['port_vs_native_mass_error']:12.3e}  "
            f"{row['H_evolution_vs_log_orbit_error']:15.3e}  "
            f"{row['poisson_state_error']:13.3e}  "
            f"{row['native_characteristic_norm']:12.5e}  "
            f"{cosine_text:>20}"
        )
    print("=" * 88)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cameras", default="2,3,4,5,6,7")
    parser.add_argument("--cutoff", type=int, default=8)
    parser.add_argument(
        "--times",
        default="0,7,14.134725141734695,30.424876125859512",
    )
    parser.add_argument(
        "--skip-spectrum",
        action="store_true",
        help="skip the dense finite spectrum comparison for larger cutoffs",
    )
    parser.add_argument("--json-out", type=Path)
    parser.add_argument(
        "--print-json",
        action="store_true",
        help="print full JSON instead of the compact human-readable summary",
    )
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    try:
        cameras = native.parse_cameras(args.cameras)
        times = parse_times(args.times)
    except ValueError as exc:
        parser.error(str(exc))
    if args.cutoff < 1:
        parser.error("cutoff must be positive")

    report = build_demo(cameras, args.cutoff, times, spectrum=not args.skip_spectrum)
    payload = json.dumps(report, indent=2, sort_keys=True)
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(payload + "\n", encoding="utf-8")
    if args.print_json:
        print(payload)
    else:
        print_summary(report)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
