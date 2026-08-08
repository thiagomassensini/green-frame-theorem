#!/usr/bin/env python3
"""UNWEIGHTED CONTROL for a Green-boundary-return characteristic audit.

This file is retained as a Euclidean q=1 comparison only.  It is not the
physical Green model of carry geometry: the physical tower already carries
q_b=b**(-1/2), and its atlas must be normalized by the carry-quadratic frame.
The corrected experiment is

    native_carry_quadratic_weighted_green_atlas_lab.py

The finite native state is factored through the exact second-difference TFVD

    f = G B f + R Tr f.

The raw port chart J=(B,Tr) is invertible but not Euclidean-unitary.  Giving
its port space the induced metric M=(G,R)* (G,R) makes J an isometry.  After
canonical whitening, the logarithmic generator becomes a standard Hermitian
operator and the native resultants remain exact observation ports.

A second construction completes the normalized native readout to a lossless
multiport characteristic matrix.  The native resultant is recovered as its
visible transmission block, up to fixed invertible normalizations.  This is a
control realization, not a candidate for the final physical self-adjoint
extension.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any, Callable, Sequence

import numpy as np

import native_carry_collective_operator_lab as collective
import native_carry_conservative_all_bases_atlas_lab as conservative
import native_carry_primitive_real_operator_all_bases_fixed as native


def tfvd_matrices(size: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Return J=(B,Tr), S=(G,R), with S J = J S = I."""
    if size < 2:
        raise ValueError("size must be at least two")

    bracket = np.zeros((max(0, size - 2), size), dtype=np.float64)
    for row in range(size - 2):
        bracket[row, row] = 1.0
        bracket[row, row + 1] = -2.0
        bracket[row, row + 2] = 1.0

    trace = np.zeros((2, size), dtype=np.float64)
    trace[0, 0] = 1.0
    trace[1, 0] = -1.0
    trace[1, 1] = 1.0
    analysis = np.vstack((bracket, trace))

    green = np.zeros((size, max(0, size - 2)), dtype=np.float64)
    for vertex in range(2, size):
        for curvature in range(vertex - 1):
            green[vertex, curvature] = float(vertex - curvature - 1)

    boundary_return = np.zeros((size, 2), dtype=np.float64)
    boundary_return[:, 0] = 1.0
    boundary_return[:, 1] = np.arange(size, dtype=np.float64)
    synthesis = np.hstack((green, boundary_return))
    return analysis, synthesis, bracket


def positive_sqrt_and_inverse(matrix: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    if float(eigenvalues[0]) <= 0.0:
        raise RuntimeError("metric is not positive definite")
    square_root = (eigenvectors * np.sqrt(eigenvalues)[None, :]) @ eigenvectors.T
    inverse_square_root = (
        eigenvectors * (1.0 / np.sqrt(eigenvalues))[None, :]
    ) @ eigenvectors.T
    return square_root, inverse_square_root


def inverse_sqrt_and_sqrt(matrix: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    if float(eigenvalues[0]) <= 0.0:
        raise RuntimeError("Gram matrix is not positive definite")
    inverse_square_root = (
        eigenvectors * (1.0 / np.sqrt(eigenvalues))[None, :]
    ) @ eigenvectors.T
    square_root = (eigenvectors * np.sqrt(eigenvalues)[None, :]) @ eigenvectors.T
    return inverse_square_root, square_root


def complete_rows_to_unitary(rows: np.ndarray) -> np.ndarray:
    """Complete orthonormal rows to a square unitary matrix."""
    row_count, dimension = rows.shape
    if row_count > dimension:
        raise ValueError("too many rows")
    defect = np.linalg.norm(rows @ rows.conjugate().T - np.eye(row_count), ord=2)
    if defect > 2.0e-10:
        raise ValueError(f"rows are not orthonormal: defect={defect}")
    _, _, right_vectors = np.linalg.svd(rows, full_matrices=True)
    complement = right_vectors[row_count:, :]
    return np.vstack((rows, complement))


def unitary_with_first_column(vector: np.ndarray) -> np.ndarray:
    """Real Householder completion for a normalized real vector."""
    vector = np.asarray(vector, dtype=np.float64)
    norm = float(np.linalg.norm(vector))
    if abs(norm - 1.0) > 2.0e-12:
        raise ValueError("first column must have unit norm")
    first = np.zeros(vector.size, dtype=np.float64)
    first[0] = 1.0
    difference = first - vector
    difference_norm_sq = float(np.dot(difference, difference))
    if difference_norm_sq < 1.0e-28:
        return np.eye(vector.size, dtype=np.float64)
    return np.eye(vector.size, dtype=np.float64) - 2.0 * np.outer(
        difference, difference
    ) / difference_norm_sq


def refine_collective_time(
    models: Sequence[native.CameraModel],
    lower: float,
    upper: float,
    state_block: int,
) -> tuple[float, float]:
    def objective(value: float) -> float:
        _, scores, _ = collective.evaluate_one(value, models, state_block)
        return float(np.sum(scores))

    return collective.golden_minimize(objective, lower, upper, steps=70)


def tfvd_metric_audit(
    size: int,
    logarithmic_generator: np.ndarray,
    state: np.ndarray,
    camera_matrix: np.ndarray,
) -> tuple[dict[str, Any], dict[str, np.ndarray]]:
    analysis, synthesis, bracket = tfvd_matrices(size)
    del bracket
    identity = np.eye(size, dtype=np.float64)
    metric = synthesis.T @ synthesis
    polar_left, _, polar_right = np.linalg.svd(analysis, full_matrices=True)
    port_unitary = polar_left @ polar_right
    # Stable polar realization of M^(1/2) and M^(-1/2).  Core operations below
    # use the orthogonal polar factor directly and avoid magnifying the Green
    # chart condition number.
    metric_sqrt = port_unitary @ synthesis
    metric_inverse_sqrt = analysis @ port_unitary.T
    port_generator_raw = analysis @ logarithmic_generator @ synthesis
    port_generator = port_unitary @ logarithmic_generator @ port_unitary.T

    raw_ports = analysis @ state
    white_ports = port_unitary @ state
    reconstructed = synthesis @ raw_ports
    reconstructed_from_white = port_unitary.T @ white_ports
    port_readout = camera_matrix @ port_unitary.T

    curvature_count = size - 2
    curvature = raw_ports[:curvature_count]
    trace = raw_ports[curvature_count:]
    bulk_resultant = camera_matrix @ synthesis[:, :curvature_count] @ curvature
    boundary_resultant = camera_matrix @ synthesis[:, curvature_count:] @ trace
    direct_resultant = camera_matrix @ state
    balance_rows: list[dict[str, Any]] = []
    for index in range(camera_matrix.shape[0]):
        bulk_norm = float(abs(bulk_resultant[index]))
        boundary_norm = float(abs(boundary_resultant[index]))
        denominator = bulk_norm * boundary_norm
        cosine = (
            float(
                np.real(
                    np.conjugate(bulk_resultant[index])
                    * boundary_resultant[index]
                )
                / denominator
            )
            if denominator > 0.0
            else None
        )
        balance_rows.append(
            {
                "index": index,
                "bulk_norm": bulk_norm,
                "boundary_norm": boundary_norm,
                "bulk_boundary_cosine": cosine,
                "boundary_to_bulk_magnitude_ratio": (
                    boundary_norm / bulk_norm if bulk_norm > 0.0 else None
                ),
                "resultant_norm": float(abs(direct_resultant[index])),
            }
        )

    bulk_metric = metric[:curvature_count, :curvature_count]
    trace_metric = metric[curvature_count:, curvature_count:]
    cross_metric = metric[:curvature_count, curvature_count:]
    true_port_energy = float(np.vdot(synthesis @ raw_ports, synthesis @ raw_ports).real)
    naive_port_energy = float(np.vdot(raw_ports, raw_ports).real)

    raw_slope_leakage = float(
        np.linalg.norm(port_generator_raw[-1, :-1])
    )
    raw_slope_row_norm = float(np.linalg.norm(port_generator_raw[-1, :]))
    slope_zero_relative_leakage = (
        raw_slope_leakage / raw_slope_row_norm if raw_slope_row_norm else 0.0
    )

    synthesis_singular_values = np.linalg.svd(synthesis, compute_uv=False)
    raw_m_selfadjoint_defect = (
        port_generator_raw.conjugate().T @ metric
        - metric @ port_generator_raw
    )
    raw_m_scale = max(
        float(np.linalg.norm(metric @ port_generator_raw, ord=2)), 1.0e-300
    )
    report = {
        "size": size,
        "identities": {
            "S_J_minus_I": float(np.linalg.norm(synthesis @ analysis - identity, ord=2)),
            "J_S_minus_I": float(np.linalg.norm(analysis @ synthesis - identity, ord=2)),
            "J_star_M_J_minus_I": float(
                np.linalg.norm(analysis.T @ metric @ analysis - identity, ord=2)
            ),
            "white_port_unitarity_error": float(
                np.linalg.norm(port_unitary.T @ port_unitary - identity, ord=2)
            ),
        },
        "metric": {
            "minimum_eigenvalue": float(synthesis_singular_values[-1] ** 2),
            "maximum_eigenvalue": float(synthesis_singular_values[0] ** 2),
            "condition_number": float(
                (synthesis_singular_values[0] / synthesis_singular_values[-1]) ** 2
            ),
            "polar_metric_square_root_error": float(
                np.linalg.norm(metric_sqrt.T @ metric_sqrt - metric, ord=2)
            ),
            "polar_whitener_inverse_error": float(
                np.linalg.norm(metric_sqrt @ metric_inverse_sqrt - identity, ord=2)
            ),
            "bulk_trace_cross_block_norm": float(np.linalg.norm(cross_metric, ord=2)),
            "bulk_metric_norm": float(np.linalg.norm(bulk_metric, ord=2)),
            "trace_metric_norm": float(np.linalg.norm(trace_metric, ord=2)),
            "state_energy": float(np.vdot(state, state).real),
            "induced_port_energy": true_port_energy,
            "naive_euclidean_port_energy": naive_port_energy,
            "induced_energy_error": abs(
                float(np.vdot(state, state).real) - true_port_energy
            ),
        },
        "selfadjoint_generator": {
            "definition": "H_GBR=M^(1/2) J L S M^(-1/2)",
            "standard_hermitian_error": float(
                np.linalg.norm(port_generator - port_generator.conjugate().T, ord=2)
            ),
            "raw_M_selfadjoint_error": float(
                np.linalg.norm(raw_m_selfadjoint_defect, ord=2)
            ),
            "raw_M_selfadjoint_relative_error": float(
                np.linalg.norm(raw_m_selfadjoint_defect, ord=2) / raw_m_scale
            ),
            "unitary_equivalence_error": float(
                np.linalg.norm(
                    port_generator
                    - port_unitary @ logarithmic_generator @ port_unitary.T,
                    ord=2,
                )
            ),
        },
        "reconstruction": {
            "raw_port_reconstruction_error": float(np.linalg.norm(reconstructed - state)),
            "white_port_reconstruction_error": float(
                np.linalg.norm(reconstructed_from_white - state)
            ),
            "native_readout_from_white_ports_error": float(
                np.max(np.abs(port_readout @ white_ports - direct_resultant))
            ),
        },
        "bulk_boundary_balance": {
            "bulk_resultants": [
                [float(value.real), float(value.imag)] for value in bulk_resultant
            ],
            "boundary_resultants": [
                [float(value.real), float(value.imag)] for value in boundary_resultant
            ],
            "direct_resultants": [
                [float(value.real), float(value.imag)] for value in direct_resultant
            ],
            "maximum_balance_error": float(
                np.max(np.abs(bulk_resultant + boundary_resultant - direct_resultant))
            ),
            "camera_balance_rows": balance_rows,
        },
        "Gamma1_zero_negative_test": {
            "Gamma1": "raw affine slope trace f(2)-f(1)",
            "relative_leakage_from_slope_zero_subspace_under_J_L_S": (
                slope_zero_relative_leakage
            ),
            "conclusion": (
                "The raw Gamma1=0 sector is not invariant under logarithmic evolution; "
                "the boundary slope must remain an explicit port unless a different "
                "fixed Green-symmetric boundary relation is derived."
            ),
        },
    }
    context = {
        "analysis": analysis,
        "synthesis": synthesis,
        "metric": metric,
        "metric_sqrt": metric_sqrt,
        "metric_inverse_sqrt": metric_inverse_sqrt,
        "port_unitary": port_unitary,
        "port_generator": port_generator,
        "white_ports": white_ports,
        "port_readout": port_readout,
    }
    return report, context


def atlas_green_lift_audit(
    size: int,
    tfvd_context: dict[str, np.ndarray],
    state: np.ndarray,
    camera_matrix: np.ndarray,
) -> dict[str, Any]:
    all_bases, _, _, weights = conservative.all_bases_weights(size)
    atlas_analysis, _, _ = conservative.analysis_matrix(all_bases, weights)
    j_matrix = tfvd_context["analysis"]
    synthesis = tfvd_context["synthesis"]
    port_unitary = tfvd_context["port_unitary"]

    atlas_to_raw_ports = j_matrix @ atlas_analysis.T
    raw_ports_to_atlas = atlas_analysis @ synthesis
    white_ports_to_atlas = atlas_analysis @ port_unitary.T
    atlas_native_readout = camera_matrix @ atlas_analysis.T
    white_port_readout = camera_matrix @ port_unitary.T

    port_identity = np.eye(size, dtype=np.float64)
    rng = np.random.default_rng(271828)
    arbitrary_atlas = rng.normal(size=atlas_analysis.shape[0]) + 1j * rng.normal(
        size=atlas_analysis.shape[0]
    )
    coherent_projection = atlas_analysis @ (atlas_analysis.T @ arbitrary_atlas)
    returned_projection = raw_ports_to_atlas @ (
        atlas_to_raw_ports @ arbitrary_atlas
    )
    atlas_state = atlas_analysis @ state
    white_ports = port_unitary @ state

    return {
        "atlas_dimension": int(atlas_analysis.shape[0]),
        "port_dimension": size,
        "port_analysis_synthesis_identity_error": float(
            np.linalg.norm(atlas_to_raw_ports @ raw_ports_to_atlas - port_identity, ord=2)
        ),
        "atlas_return_equals_sync_projection_error": float(
            np.linalg.norm(returned_projection - coherent_projection)
        ),
        "white_port_to_atlas_state_error": float(
            np.linalg.norm(white_ports_to_atlas @ white_ports - atlas_state)
        ),
        "native_readout_intertwining_error": float(
            np.max(
                np.abs(
                    atlas_native_readout @ (white_ports_to_atlas @ white_ports)
                    - white_port_readout @ white_ports
                )
            )
        ),
        "identity": (
            "A [G,R] (B,Tr) A* = Pi_sync and (B,Tr) A* A [G,R] = I_ports"
        ),
    }


def characteristic_audit(
    time_value: float,
    logarithmic_generator: np.ndarray,
    amplitude: np.ndarray,
    camera_matrix: np.ndarray,
    tfvd_context: dict[str, np.ndarray],
) -> dict[str, Any]:
    size = amplitude.size
    camera_count = camera_matrix.shape[0]
    camera_gram = camera_matrix @ camera_matrix.T
    gram_inverse_sqrt, gram_sqrt = inverse_sqrt_and_sqrt(camera_gram)
    coisometric_readout = gram_inverse_sqrt @ camera_matrix

    port_unitary = tfvd_context["port_unitary"]
    port_generator = tfvd_context["port_generator"]
    port_readout = coisometric_readout @ port_unitary.T
    port_input = port_unitary @ (amplitude / np.linalg.norm(amplitude))
    output_completion = complete_rows_to_unitary(port_readout)
    input_completion = unitary_with_first_column(port_input)

    logarithms = np.diag(logarithmic_generator).astype(np.float64)
    phases = np.exp(-1j * time_value * logarithms)
    number_propagator = np.diag(phases)
    port_propagator = port_unitary @ number_propagator @ port_unitary.T
    characteristic = output_completion @ port_propagator @ input_completion

    visible_block = characteristic[:camera_count, 0]
    hidden_block = characteristic[camera_count:, 0]
    native_resultant = camera_matrix @ (
        phases * amplitude.astype(np.complex128)
    )
    reconstructed_native = (
        np.linalg.norm(amplitude) * gram_sqrt @ visible_block
    )

    generator_spectrum_error = float(
        np.max(
            np.abs(
                np.linalg.eigvalsh(port_generator)
                - np.sort(logarithms)
            )
        )
    )

    sample_moduli: list[float] = []
    maximum_unitarity_error = 0.0
    for sample_time in np.linspace(0.0, 50.0, 11):
        sample_phases = np.exp(-1j * sample_time * logarithms)
        sample_propagator = port_unitary @ np.diag(sample_phases) @ port_unitary.T
        sample_characteristic = (
            output_completion @ sample_propagator @ input_completion
        )
        maximum_unitarity_error = max(
            maximum_unitarity_error,
            float(
                np.linalg.norm(
                    sample_characteristic.conjugate().T @ sample_characteristic
                    - np.eye(size),
                    ord=2,
                )
            ),
        )
        sample_native = camera_matrix @ (sample_phases * amplitude)
        sample_moduli.append(float(np.linalg.norm(sample_native)))

    visible_energy = float(np.vdot(visible_block, visible_block).real)
    hidden_energy = float(np.vdot(hidden_block, hidden_block).real)
    return {
        "time": time_value,
        "definition": (
            "Theta(t)=U_out exp(-it H_GBR) U_in; U_out and U_in are fixed unitary "
            "completions of the native readout and fixed carry-mass input."
        ),
        "dimension": size,
        "visible_camera_channels": camera_count,
        "hidden_complement_channels": size - camera_count,
        "maximum_characteristic_unitarity_error": maximum_unitarity_error,
        "port_generator_spectrum_error_vs_log_n": generator_spectrum_error,
        "visible_transmission_block": [
            [float(value.real), float(value.imag)] for value in visible_block
        ],
        "native_resultants": [
            [float(value.real), float(value.imag)] for value in native_resultant
        ],
        "native_resultant_reconstruction_error": float(
            np.max(np.abs(reconstructed_native - native_resultant))
        ),
        "visible_energy": visible_energy,
        "hidden_energy": hidden_energy,
        "lossless_energy_ledger_error": abs(1.0 - visible_energy - hidden_energy),
        "native_norm_variation_on_real_axis": {
            "minimum": min(sample_moduli),
            "maximum": max(sample_moduli),
            "ratio_max_to_min": max(sample_moduli) / max(min(sample_moduli), 1.0e-300),
        },
        "characteristic_function_firewall": (
            "The native resultant is not the whole scalar characteristic function: "
            "its real-axis modulus varies. It is exactly a visible transmission "
            "subblock of the larger unitary characteristic matrix. Missing visible "
            "energy is carried by the hidden complementary ports."
        ),
        "selfadjoint_delay_candidate": {
            "edge_lengths": "ell_n=log n; n=1 is a zero-delay seed/direct port",
            "edge_equation": "first-order propagation gives exp(-it ell_n)",
            "fixed_endpoint_couplers": "U_in and U_out",
            "status": (
                "finite lossless characteristic realization constructed; proving it "
                "as the characteristic matrix of one fixed maximal self-adjoint "
                "infinite extension remains open"
            ),
        },
    }


def run_lab(args: argparse.Namespace) -> dict[str, Any]:
    cameras = native.parse_cameras(args.cameras)
    models = [native.build_camera_model(camera, args.cutoff) for camera in cameras]
    camera_matrix, size = collective.native_readout_matrix(models)
    blind_time, score_sum = refine_collective_time(
        models, args.refine_lower, args.refine_upper, args.state_block
    )

    numbers = np.arange(1, size + 1, dtype=np.float64)
    logarithmic_generator = np.diag(np.log(numbers))
    amplitude = numbers ** -0.5
    state = amplitude * np.exp(-1j * blind_time * np.log(numbers))

    tfvd_report, tfvd_context = tfvd_metric_audit(
        size, logarithmic_generator, state, camera_matrix
    )
    return {
        "schema": "org.native-carry.green-boundary-characteristic/v1",
        "status": "FINITE_GBR_CONSERVATIVE_CHARACTERISTIC_AUDIT",
        "native_operator_authority": (
            "native_carry_primitive_real_operator_all_bases_fixed.py"
        ),
        "configuration": {
            "cameras": list(cameras),
            "cutoff": args.cutoff,
            "ambient_dimension": size,
            "refined_blind_time": blind_time,
            "sum_native_scores_at_refined_time": score_sum,
        },
        "green_boundary_return": tfvd_report,
        "atlas_green_lift": atlas_green_lift_audit(
            size, tfvd_context, state, camera_matrix
        ),
        "lossless_characteristic": characteristic_audit(
            blind_time,
            logarithmic_generator,
            amplitude,
            camera_matrix,
            tfvd_context,
        ),
        "separation_of_roles": {
            "native_operator": "C_native exp(-itL) alpha",
            "TFVD": "invertible bulk-boundary coordinate chart",
            "port_metric": "makes TFVD conservative without deleting cross terms",
            "H_GBR": "self-adjoint logarithmic generator in whitened GBR ports",
            "Theta": "unitary characteristic matrix with native visible subblock",
            "remaining_gate": (
                "derive a fixed Green-symmetric maximal boundary relation whose "
                "closed-loop characteristic condition is equivalent to native blindness"
            ),
        },
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cameras", default="2,3,4,5,6,7")
    parser.add_argument("--cutoff", type=int, default=32)
    parser.add_argument("--refine-lower", type=float, default=14.12)
    parser.add_argument("--refine-upper", type=float, default=14.15)
    parser.add_argument("--state-block", type=int, default=512)
    parser.add_argument("--output", type=Path)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    if args.cutoff < 1 or args.state_block < 1:
        parser.error("cutoff and state-block must be positive")
    if args.refine_upper <= args.refine_lower:
        parser.error("refine-upper must be larger than refine-lower")
    report = run_lab(args)
    payload = json.dumps(report, indent=2, sort_keys=True)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload + "\n", encoding="utf-8")
    print(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
