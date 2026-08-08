#!/usr/bin/env python3
"""Global conservative gluing audit for the carry-weighted Green atlas.

The local physical scale is fixed before gluing:

    q_b = b**(-1/2),
    A_q = q**(-1) (I-qU)**2,
    V = stack_b(A_b) [sum_b A_b* A_b]**(-1/2),  V*V=I.

Two distinct global gluings are then audited.

1. The coherence reflection J_sync=2VV*-I glues duplicated camera charts.
   It is necessary but fixes every coherent orbit, hence cannot select blind
   times.

2. The signed native camera incidence C defines the coisometry

       Q=(CC*)**(-1/2) C V*,

   and the canonical visible-channel reflection

       J_vis=I-2Q*Q.

The two commuting reflections combine into the global gluing

       U_glue=J_sync J_vis=2(VV*-Q*Q)-I.

Its +1 sector is exactly ran(V) intersect ker(Q): coherent and blind.  Thus

    C psi(t)=0
       iff U_glue V psi(t)=V psi(t).

Moreover the native characteristic energy is exactly the reflection defect

    ||Q z(t)||**2 = (1/4)||[I-U_glue]z(t)||**2.

The multiplicative incidence graph n -> b n is also audited.  Its connection
phase exp(-it log b) is flat on every arithmetic square; nontrivial selection
therefore comes from the enriched signed camera incidence, not from bare
multiplicative holonomy.

This is a finite boundary-colligation candidate.  It does not yet prove that
the assembled weighted traces form the final infinite maximal boundary triple.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any, Callable, Sequence

import numpy as np

import native_carry_collective_operator_lab as collective
import native_carry_primitive_real_operator_all_bases_fixed as native
import native_carry_quadratic_weighted_green_atlas_lab as quadratic


def positive_sqrt_and_inverse(matrix: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    if float(eigenvalues[0]) <= 0.0:
        raise RuntimeError("matrix must be positive definite")
    square_root = (eigenvectors * np.sqrt(eigenvalues)[None, :]) @ eigenvectors.T
    inverse_square_root = (
        eigenvectors * (1.0 / np.sqrt(eigenvalues))[None, :]
    ) @ eigenvectors.T
    return square_root, inverse_square_root


def refine_minimum(
    function: Callable[[float], float], lower: float, upper: float
) -> tuple[float, float]:
    return collective.golden_minimize(function, lower, upper, steps=70)


def multiplicative_incidence_audit(
    bases: Sequence[int], size: int, time_value: float, state: np.ndarray
) -> dict[str, Any]:
    edges = [
        (source, base * source, base)
        for base in bases
        for source in range(1, size // base + 1)
    ]

    parent = list(range(size + 1))

    def find(vertex: int) -> int:
        while parent[vertex] != vertex:
            parent[vertex] = parent[parent[vertex]]
            vertex = parent[vertex]
        return vertex

    def union(left: int, right: int) -> None:
        left_root = find(left)
        right_root = find(right)
        if left_root != right_root:
            parent[right_root] = left_root

    for source, target, _ in edges:
        union(source, target)
    component_count = len({find(vertex) for vertex in range(1, size + 1)})
    cycle_rank = len(edges) - size + component_count

    maximum_edge_gradient_error = 0.0
    maximum_physical_transport_error = 0.0
    for source, target, base in edges:
        phase = np.exp(-1j * time_value * math.log(base))
        gradient_phase = np.exp(
            -1j * time_value * (math.log(target) - math.log(source))
        )
        maximum_edge_gradient_error = max(
            maximum_edge_gradient_error, float(abs(phase - gradient_phase))
        )
        q = base ** -0.5
        maximum_physical_transport_error = max(
            maximum_physical_transport_error,
            float(abs(state[target - 1] / q - phase * state[source - 1])),
        )

    square_count = 0
    maximum_square_path_error = 0.0
    maximum_square_holonomy_error = 0.0
    for first_index, first_base in enumerate(bases):
        for second_base in bases[first_index + 1 :]:
            for _source in range(1, size // (first_base * second_base) + 1):
                first_phase = np.exp(-1j * time_value * math.log(first_base))
                second_phase = np.exp(-1j * time_value * math.log(second_base))
                path_one = first_phase * second_phase
                path_two = second_phase * first_phase
                holonomy = path_one * np.conjugate(path_two)
                maximum_square_path_error = max(
                    maximum_square_path_error, float(abs(path_one - path_two))
                )
                maximum_square_holonomy_error = max(
                    maximum_square_holonomy_error, float(abs(holonomy - 1.0))
                )
                square_count += 1

    return {
        "vertex_count": size,
        "directed_edge_count": len(edges),
        "undirected_component_count": component_count,
        "cycle_rank": cycle_rank,
        "arithmetic_square_count": square_count,
        "maximum_edge_log_gradient_error": maximum_edge_gradient_error,
        "maximum_carry_normalized_transport_error": (
            maximum_physical_transport_error
        ),
        "maximum_square_path_error": maximum_square_path_error,
        "maximum_square_holonomy_error": maximum_square_holonomy_error,
        "conclusion": (
            "The bare multiplicative connection is exact/flat even when the "
            "incidence graph has cycles; it cannot select blind times alone."
        ),
    }


def build_quadratic_atlas(
    bases: Sequence[int], size: int
) -> tuple[np.ndarray, np.ndarray, list[quadratic.TowerChart]]:
    charts = [quadratic.build_tower_chart(base, size) for base in bases]
    stacked = np.vstack([chart.canonical_analysis for chart in charts])
    frame = stacked.T @ stacked
    inverse_sqrt, _ = quadratic.inverse_positive_sqrt(frame)
    analysis = stacked @ inverse_sqrt
    return analysis, frame, charts


def random_involution_audit(
    action: Callable[[np.ndarray], np.ndarray], dimension: int, seed: int
) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    left = rng.normal(size=dimension) + 1j * rng.normal(size=dimension)
    right = rng.normal(size=dimension) + 1j * rng.normal(size=dimension)
    action_left = action(left)
    action_right = action(right)
    return {
        "involution_relative_error": float(
            np.linalg.norm(action(action(left)) - left) / np.linalg.norm(left)
        ),
        "norm_conservation_relative_error": float(
            abs(np.linalg.norm(action_left) - np.linalg.norm(left))
            / np.linalg.norm(left)
        ),
        "self_adjoint_pairing_relative_error": float(
            abs(np.vdot(left, action_right) - np.vdot(action_left, right))
            / (np.linalg.norm(left) * np.linalg.norm(right))
        ),
    }


def gluing_audit(
    atlas: np.ndarray,
    camera_matrix: np.ndarray,
    amplitude: np.ndarray,
    logarithms: np.ndarray,
    native_time: float,
) -> dict[str, Any]:
    atlas_dimension, state_dimension = atlas.shape
    camera_gram = camera_matrix @ camera_matrix.T
    camera_sqrt, camera_inverse_sqrt = positive_sqrt_and_inverse(camera_gram)
    readout = camera_inverse_sqrt @ camera_matrix @ atlas.T

    def sync_projection(vector: np.ndarray) -> np.ndarray:
        return atlas @ (atlas.T @ vector)

    def sync_reflection(vector: np.ndarray) -> np.ndarray:
        return 2.0 * sync_projection(vector) - vector

    def generator_action(vector: np.ndarray) -> np.ndarray:
        return atlas @ (logarithms * (atlas.T @ vector))

    def visible_projection(vector: np.ndarray) -> np.ndarray:
        return readout.T @ (readout @ vector)

    def blind_reflection(vector: np.ndarray) -> np.ndarray:
        return vector - 2.0 * visible_projection(vector)

    def physical_blind_projection(vector: np.ndarray) -> np.ndarray:
        return sync_projection(vector) - visible_projection(vector)

    def global_reflection(vector: np.ndarray) -> np.ndarray:
        return 2.0 * physical_blind_projection(vector) - vector

    rng = np.random.default_rng(20260805)
    commutator_vector = rng.normal(size=atlas_dimension) + 1j * rng.normal(
        size=atlas_dimension
    )
    sync_commutator_error = float(
        np.linalg.norm(
            sync_reflection(generator_action(commutator_vector))
            - generator_action(sync_reflection(commutator_vector))
        )
        / np.linalg.norm(commutator_vector)
    )

    amplitude_norm = float(np.linalg.norm(amplitude))

    def orbit(time_value: float) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
        state = amplitude * np.exp(-1j * time_value * logarithms)
        atlas_state = atlas @ (state / amplitude_norm)
        visible = readout @ atlas_state
        return state, atlas_state, visible

    def visible_energy(time_value: float) -> float:
        _, _, visible = orbit(time_value)
        return float(np.vdot(visible, visible).real)

    characteristic_time, characteristic_minimum = refine_minimum(
        visible_energy, 14.12, 14.15
    )
    sample_times = (0.0, 7.0, native_time, characteristic_time, 30.0)
    samples: list[dict[str, Any]] = []
    maximum_characteristic_identity_error = 0.0
    maximum_native_unwhitening_error = 0.0
    maximum_sync_fixed_error = 0.0
    for time_value in sample_times:
        state, atlas_state, visible = orbit(time_value)
        reflection_defect = 0.5 * (atlas_state - global_reflection(atlas_state))
        defect_energy = float(np.vdot(reflection_defect, reflection_defect).real)
        visible_value = float(np.vdot(visible, visible).real)
        characteristic_error = abs(defect_energy - visible_value)
        unwhitened = amplitude_norm * camera_sqrt @ visible
        native_resultant = camera_matrix @ state
        unwhitening_error = float(np.max(np.abs(unwhitened - native_resultant)))
        sync_fixed_error = float(
            np.linalg.norm(sync_reflection(atlas_state) - atlas_state)
        )
        maximum_characteristic_identity_error = max(
            maximum_characteristic_identity_error, characteristic_error
        )
        maximum_native_unwhitening_error = max(
            maximum_native_unwhitening_error, unwhitening_error
        )
        maximum_sync_fixed_error = max(
            maximum_sync_fixed_error, sync_fixed_error
        )
        samples.append(
            {
                "time": time_value,
                "visible_characteristic_energy": visible_value,
                "blind_reflection_defect_energy": defect_energy,
                "sync_reflection_fixed_point_error": sync_fixed_error,
                "native_resultant_norm": float(np.linalg.norm(native_resultant)),
            }
        )

    coherent_native_state = orbit(native_time)[1]
    blind_fixed_point_defect = float(
        np.linalg.norm(
            global_reflection(coherent_native_state) - coherent_native_state
        )
    )
    camera_coisometry_error = float(
        np.linalg.norm(
            readout @ readout.T - np.eye(camera_matrix.shape[0]), ord=2
        )
    )
    sector_rng = np.random.default_rng(20260808)
    sector_probe = sector_rng.normal(size=atlas_dimension) + 1j * sector_rng.normal(
        size=atlas_dimension
    )
    visible_probe = visible_projection(sector_probe)
    coherent_blind_probe = physical_blind_projection(sector_probe)
    incoherent_probe = sector_probe - sync_projection(sector_probe)
    blind_sector_fixed_error = float(
        np.linalg.norm(
            global_reflection(coherent_blind_probe) - coherent_blind_probe
        )
        / max(np.linalg.norm(coherent_blind_probe), np.finfo(np.float64).tiny)
    )
    visible_sector_sign_error = float(
        np.linalg.norm(global_reflection(visible_probe) + visible_probe)
        / max(np.linalg.norm(visible_probe), np.finfo(np.float64).tiny)
    )
    incoherent_sector_sign_error = float(
        np.linalg.norm(global_reflection(incoherent_probe) + incoherent_probe)
        / max(np.linalg.norm(incoherent_probe), np.finfo(np.float64).tiny)
    )
    reflection_commutator_error = float(
        np.linalg.norm(
            sync_reflection(blind_reflection(sector_probe))
            - blind_reflection(sync_reflection(sector_probe))
        )
        / np.linalg.norm(sector_probe)
    )
    return {
        "atlas_dimension": atlas_dimension,
        "state_dimension": state_dimension,
        "camera_count": int(camera_matrix.shape[0]),
        "coherence_gluing": {
            "definition": "J_sync=2 V V* - I",
            "random_vector_audit": random_involution_audit(
                sync_reflection, atlas_dimension, 20260806
            ),
            "commutator_with_log_generator_action_error": sync_commutator_error,
            "maximum_coherent_orbit_fixed_point_error": maximum_sync_fixed_error,
            "selection_result": (
                "J_sync fixes the full coherent orbit for every t and therefore "
                "does not select native blind times."
            ),
        },
        "signed_native_gluing": {
            "normalized_readout": "Q=(CC*)^(-1/2) C V*",
            "camera_coisometry_error": camera_coisometry_error,
            "visible_reflection": "J_vis=I-2 Q*Q",
            "reflection_commutator_error": reflection_commutator_error,
            "definition": (
                "U_glue=J_sync J_vis=2(P_sync-P_visible)-I"
            ),
            "plus_one_sector": "ran(V) intersect ker(Q): coherent and blind",
            "minus_one_sector": (
                "ran(Q*) plus ker(V*): visible or atlas-incoherent"
            ),
            "plus_one_multiplicity": state_dimension - camera_matrix.shape[0],
            "minus_one_multiplicity": (
                atlas_dimension - state_dimension + camera_matrix.shape[0]
            ),
            "blind_sector_fixed_relative_error": blind_sector_fixed_error,
            "visible_sector_minus_sign_relative_error": visible_sector_sign_error,
            "incoherent_sector_minus_sign_relative_error": (
                incoherent_sector_sign_error
            ),
            "random_vector_audit": random_involution_audit(
                global_reflection, atlas_dimension, 20260807
            ),
            "maximum_characteristic_identity_error": (
                maximum_characteristic_identity_error
            ),
            "maximum_native_unwhitening_error": maximum_native_unwhitening_error,
            "native_time_fixed_point_defect": blind_fixed_point_defect,
            "characteristic_identity": (
                "||Q z(t)||^2 = (1/4)||[I-U_glue]z(t)||^2; native resultants "
                "are recovered by ||alpha||(CC*)^(1/2)Qz(t)."
            ),
            "boundary_relation_candidate": (
                "(U_glue-I)Gamma_0+i(U_glue+I)Gamma_1=0, equivalently "
                "P_(visible+incoherent) Gamma_0=0 and "
                "P_(coherent blind) Gamma_1=0."
            ),
        },
        "native_score_refined_time": native_time,
        "characteristic_refined_time": characteristic_time,
        "refined_time_difference": abs(characteristic_time - native_time),
        "finite_minimum_warning": (
            "Exact zero sets coincide because whitening is fixed and invertible; "
            "finite nonzero minima may differ because the native score has "
            "time-dependent camera-energy denominators."
        ),
        "characteristic_minimum_energy": characteristic_minimum,
        "samples": samples,
    }


def run_lab(args: argparse.Namespace) -> dict[str, Any]:
    cameras = native.parse_cameras(args.cameras)
    models = [native.build_camera_model(camera, args.cutoff) for camera in cameras]
    camera_matrix, size = collective.native_readout_matrix(models)
    native_time, native_score_sum = quadratic.refine_collective_time(
        models, args.state_block
    )
    numbers = np.arange(1, size + 1, dtype=np.float64)
    amplitude = numbers ** -0.5
    logarithms = np.log(numbers)
    native_state = amplitude * np.exp(-1j * native_time * logarithms)
    atlas, frame, charts = build_quadratic_atlas(cameras, size)

    return {
        "schema": "org.native-carry.global-green-gluing/v1",
        "status": "FINITE_GLOBAL_GREEN_GLUE_CANDIDATE",
        "native_operator_authority": (
            "native_carry_primitive_real_operator_all_bases_fixed.py"
        ),
        "configuration": {
            "cameras": list(cameras),
            "cutoff": args.cutoff,
            "ambient_dimension": size,
            "native_score_refined_time": native_time,
            "native_score_sum": native_score_sum,
        },
        "local_physics": {
            "tower_count_by_base": {
                str(chart.base): len(chart.towers) for chart in charts
            },
            "quadratic_frame_min_eigenvalue": float(
                np.linalg.eigvalsh(frame)[0]
            ),
            "atlas_parseval_error": float(
                np.linalg.norm(atlas.T @ atlas - np.eye(size), ord=2)
            ),
        },
        "multiplicative_incidence": multiplicative_incidence_audit(
            cameras, size, native_time, native_state
        ),
        "global_gluing": gluing_audit(
            atlas, camera_matrix, amplitude, logarithms, native_time
        ),
        "interpretation": {
            "bare_incidence": (
                "Multiplicative incidence supplies a flat phase connection and "
                "cannot select resonances by holonomy alone."
            ),
            "coherence": (
                "J_sync performs chart consistency only; it is not the selector."
            ),
            "selector": (
                "U_glue combines chart consistency with the signed native camera "
                "incidence; its fixed sector is precisely coherent and blind."
            ),
            "remaining_gate": (
                "Prove that the weighted local Green traces assemble surjectively "
                "into the boundary space on which U_glue defines the maximal "
                "self-adjoint infinite extension."
            ),
        },
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cameras", default="2,3,4,5,6,7")
    parser.add_argument("--cutoff", type=int, default=32)
    parser.add_argument("--state-block", type=int, default=512)
    parser.add_argument("--output", type=Path)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    if args.cutoff < 1 or args.state_block < 1:
        parser.error("cutoff and state-block must be positive")
    report = run_lab(args)
    payload = json.dumps(report, indent=2, sort_keys=True)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload + "\n", encoding="utf-8")
    print(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
