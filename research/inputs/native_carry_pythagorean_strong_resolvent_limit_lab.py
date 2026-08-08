#!/usr/bin/env python3
"""Strong-resolvent inductive-limit audit for the Pythagorean carry atlas.

All finite node-return/Green ports have stable arithmetic labels

    (kind, base, target integer).

This puts every cutoff in one countable universal port space.  If V_N is the
normalized analysis embedded in that space, define the finite self-adjoint
operator

    H_N = V_N L_N V_N* on ran(V_N), and 0 on ran(V_N)^perp,
    L_N = diag(log 1,...,log N).

For z outside the real axis its resolvent has the exact action

    (H_N-z)^(-1)y
      = -z^(-1)y
        + V_N [ (L_N-z)^(-1)+z^(-1) ] V_N* y.

Thus strong-star convergence V_N -> V and the elementary diagonal resolvent
convergence of L_N imply strong resolvent convergence of H_N.  This script
audits the required local embeddings, full resolvents, bulk-block resolvents,
and local Weyl actions against a larger reference cutoff.

The full transported-generator limit is structurally stronger than the old
statistical/Mosco sketches found elsewhere in the research server: it uses
only stable carry labels, bounded Pythagorean analysis, and exact functional
calculus.  Bulk-block and Weyl convergence are audited numerically here but
remain a separate form-domain theorem.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import native_carry_conservative_all_bases_atlas_lab as conservative
import native_carry_pythagorean_node_weyl_colligation_lab as node_weyl
import native_carry_quadratic_weighted_green_atlas_lab as green


PortLabel = tuple[str, int, int]


def parse_sizes(text: str) -> tuple[int, ...]:
    values = tuple(sorted({int(part.strip()) for part in text.split(",") if part.strip()}))
    if len(values) < 2 or any(value < 8 for value in values):
        raise ValueError("provide at least two distinct sizes >= 8")
    return values


def port_labels(size: int) -> tuple[list[PortLabel], list[PortLabel]]:
    _, depths, _, _ = conservative.all_bases_weights(size)
    endpoint: list[PortLabel] = [("node", 0, 1)]
    green_endpoint: list[PortLabel] = []
    bulk: list[PortLabel] = []

    for base_index, base in enumerate(range(2, size + 1)):
        endpoint.extend(
            ("node", base, int(number))
            for number in np.flatnonzero(depths[base_index] == 1) + 1
        )

    for base_index, base in enumerate(range(2, size + 1)):
        chart = green.build_tower_chart(base, size)
        numbers = np.asarray(
            [number for _, tower in chart.towers for number in tower],
            dtype=np.int64,
        )
        row_depths = depths[base_index, numbers - 1]
        green_endpoint.extend(
            ("green_endpoint", base, int(number))
            for number in numbers[row_depths == 1]
        )
        bulk.extend(
            ("bulk", base, int(number))
            for number in numbers[row_depths >= 2]
        )
    return endpoint + green_endpoint, bulk


def embed_analysis(
    analysis: np.ndarray,
    labels: list[PortLabel],
    reference_labels: list[PortLabel],
    reference_size: int,
) -> np.ndarray:
    label_to_row = {label: row for row, label in enumerate(reference_labels)}
    rows = np.asarray([label_to_row[label] for label in labels], dtype=np.int64)
    columns = np.arange(analysis.shape[1], dtype=np.int64)
    embedded = np.zeros(
        (len(reference_labels), reference_size), dtype=np.float64
    )
    embedded[np.ix_(rows, columns)] = analysis
    return embedded


def full_resolvent_action(
    atlas: np.ndarray, parameter: complex, vector: np.ndarray
) -> np.ndarray:
    logarithms = np.log(np.arange(1, atlas.shape[1] + 1, dtype=np.float64))
    coherent = atlas.T @ vector
    multiplier = 1.0 / (logarithms - parameter) + 1.0 / parameter
    return -vector / parameter + atlas @ (multiplier * coherent)


def bulk_resolvent_action(
    bulk: np.ndarray, parameter: complex, vector: np.ndarray
) -> np.ndarray:
    logarithms = np.log(np.arange(1, bulk.shape[1] + 1, dtype=np.float64))
    h_bb = (bulk * logarithms[None, :]) @ bulk.T
    return np.linalg.solve(
        parameter * np.eye(bulk.shape[0], dtype=np.complex128) - h_bb,
        vector,
    )


def weyl_action(
    endpoint: np.ndarray,
    bulk: np.ndarray,
    parameter: complex,
    vector: np.ndarray,
) -> np.ndarray:
    logarithms = np.log(np.arange(1, endpoint.shape[1] + 1, dtype=np.float64))
    h_bb = (bulk * logarithms[None, :]) @ bulk.T
    rhs = bulk @ (logarithms * (endpoint.T @ vector))
    solved = np.linalg.solve(
        parameter * np.eye(bulk.shape[0], dtype=np.complex128) - h_bb,
        rhs,
    )
    return (
        parameter * vector
        - endpoint @ (logarithms * (endpoint.T @ vector))
        - endpoint @ (logarithms * (bulk.T @ solved))
    )


def deterministic_label_probe(
    anchor_labels: list[PortLabel], reference_labels: list[PortLabel]
) -> np.ndarray:
    reference_index = {
        label: index for index, label in enumerate(reference_labels)
    }
    vector = np.zeros(len(reference_labels), dtype=np.complex128)
    for order, label in enumerate(anchor_labels, start=1):
        vector[reference_index[label]] = (1.0 + 1.0j * order) / order
    norm = np.linalg.norm(vector)
    return vector / norm if norm > 0.0 else vector


def run_lab(args: argparse.Namespace) -> dict[str, Any]:
    sizes = parse_sizes(args.sizes)
    reference_size = sizes[-1]
    built: dict[int, dict[str, Any]] = {}
    for size in sizes:
        colligation = node_weyl.normalized_colligation(size)
        endpoint_labels, bulk_labels = port_labels(size)
        endpoint = np.asarray(colligation["endpoint"], dtype=np.float64)
        bulk = np.asarray(colligation["bulk"], dtype=np.float64)
        raw_endpoint = np.asarray(colligation["node_endpoint"], dtype=np.float64)
        raw_bulk = np.asarray(colligation["bulk_raw"], dtype=np.float64)
        if endpoint.shape[0] != len(endpoint_labels):
            raise AssertionError("endpoint labels do not match analysis rows")
        if bulk.shape[0] != len(bulk_labels):
            raise AssertionError("bulk labels do not match analysis rows")
        built[size] = {
            "colligation": colligation,
            "endpoint": endpoint,
            "bulk": bulk,
            "raw_endpoint": raw_endpoint,
            "raw_bulk": raw_bulk,
            "endpoint_labels": endpoint_labels,
            "bulk_labels": bulk_labels,
        }

    reference = built[reference_size]
    reference_endpoint_labels = reference["endpoint_labels"]
    reference_bulk_labels = reference["bulk_labels"]
    reference_all_labels = reference_endpoint_labels + reference_bulk_labels
    reference_endpoint = reference["endpoint"]
    reference_bulk = reference["bulk"]
    reference_atlas = np.vstack((reference_endpoint, reference_bulk))

    anchor_size = sizes[0]
    anchor = built[anchor_size]
    state_probe = np.zeros(reference_size, dtype=np.complex128)
    support = min(args.probe_support, anchor_size)
    state_probe[:support] = np.arange(1, support + 1, dtype=np.float64)
    state_probe /= np.linalg.norm(state_probe)

    anchor_atlas = np.vstack((anchor["endpoint"], anchor["bulk"]))
    embedded_anchor_atlas = embed_analysis(
        anchor_atlas,
        anchor["endpoint_labels"] + anchor["bulk_labels"],
        reference_all_labels,
        reference_size,
    )
    full_port_probe = embedded_anchor_atlas @ state_probe
    full_port_probe /= np.linalg.norm(full_port_probe)
    endpoint_probe = deterministic_label_probe(
        anchor["endpoint_labels"], reference_endpoint_labels
    )
    bulk_probe = deterministic_label_probe(
        anchor["bulk_labels"], reference_bulk_labels
    )

    full_parameters = (1.0j, 2.0 + 1.0j)
    block_parameter = 2.0 + 0.75j
    reference_full_resolvents = {
        str(parameter): full_resolvent_action(
            reference_atlas, parameter, full_port_probe
        )
        for parameter in full_parameters
    }
    reference_bulk_resolvent = bulk_resolvent_action(
        reference_bulk, block_parameter, bulk_probe
    )
    reference_weyl = weyl_action(
        reference_endpoint, reference_bulk, block_parameter, endpoint_probe
    )

    rows: list[dict[str, Any]] = []
    for size in sizes:
        item = built[size]
        endpoint = embed_analysis(
            item["endpoint"],
            item["endpoint_labels"],
            reference_endpoint_labels,
            reference_size,
        )
        bulk = embed_analysis(
            item["bulk"],
            item["bulk_labels"],
            reference_bulk_labels,
            reference_size,
        )
        atlas = np.vstack((endpoint, bulk))
        raw_endpoint = embed_analysis(
            item["raw_endpoint"],
            item["endpoint_labels"],
            reference_endpoint_labels,
            reference_size,
        )
        raw_bulk = embed_analysis(
            item["raw_bulk"],
            item["bulk_labels"],
            reference_bulk_labels,
            reference_size,
        )
        raw_atlas = np.vstack((raw_endpoint, raw_bulk))

        common_rows = [
            reference_all_labels.index(label)
            for label in item["endpoint_labels"] + item["bulk_labels"]
        ]
        reference_raw = np.vstack(
            (reference["raw_endpoint"], reference["raw_bulk"])
        )
        raw_prefix_error = np.linalg.norm(
            raw_atlas[np.ix_(common_rows, np.arange(size))]
            - reference_raw[np.ix_(common_rows, np.arange(size))],
            ord=2,
        )

        h_bb = (
            bulk
            * np.log(np.arange(1, reference_size + 1, dtype=np.float64))[None, :]
        ) @ bulk.T
        row = {
            "ambient_dimension": size,
            "endpoint_dimension": len(item["endpoint_labels"]),
            "bulk_dimension": len(item["bulk_labels"]),
            "raw_arithmetic_prefix_error": float(raw_prefix_error),
            "normalized_analysis_fixed_state_error_to_reference": float(
                np.linalg.norm(atlas @ state_probe - reference_atlas @ state_probe)
            ),
            "synchronization_projection_probe_error_to_reference": float(
                np.linalg.norm(
                    atlas @ (atlas.T @ full_port_probe)
                    - reference_atlas @ (reference_atlas.T @ full_port_probe)
                )
            ),
            "full_resolvent_probe_errors_to_reference": {
                str(parameter): float(
                    np.linalg.norm(
                        full_resolvent_action(atlas, parameter, full_port_probe)
                        - reference_full_resolvents[str(parameter)]
                    )
                )
                for parameter in full_parameters
            },
            "bulk_block_spectrum_max": float(np.linalg.eigvalsh(h_bb)[-1]),
            "bulk_resolvent_probe_error_to_reference": float(
                np.linalg.norm(
                    bulk_resolvent_action(bulk, block_parameter, bulk_probe)
                    - reference_bulk_resolvent
                )
            ),
            "weyl_probe_error_to_reference": float(
                np.linalg.norm(
                    weyl_action(endpoint, bulk, block_parameter, endpoint_probe)
                    - reference_weyl
                )
            ),
            "endpoint_lower": item["colligation"]["audit"][
                "normalized_endpoint_min_eigenvalue"
            ],
            "poisson_norm": item["colligation"]["audit"][
                "poisson_operator_norm"
            ],
        }
        rows.append(row)

    return {
        "schema": "org.native-carry.pythagorean-strong-resolvent-limit/v1",
        "status": "FULL_STRONG_RESOLVENT_ROUTE_EXACT_BLOCK_WEYL_LIMIT_NUMERICAL",
        "configuration": {
            "sizes": list(sizes),
            "reference_size": reference_size,
            "anchor_size": anchor_size,
            "probe_support": support,
            "full_resolvent_parameters": [
                [float(value.real), float(value.imag)] for value in full_parameters
            ],
            "block_weyl_parameter": [
                float(block_parameter.real), float(block_parameter.imag)
            ],
        },
        "inductive_system": {
            "state_space": "H=l2(N)",
            "port_labels": "(kind,base,target integer)",
            "finite_analysis": "T_N=Q_N T P_N",
            "stable_rows": (
                "Every row with target n is causal in ancestors of n and is "
                "identical at every cutoff >=n."
            ),
            "uniform_bounds": "c I<=T_N*T_N<=C I",
            "normalized_analysis": "V_N=T_N(T_N*T_N)^(-1/2)",
        },
        "strong_resolvent_argument": {
            "finite_operator": (
                "H_N=V_N L_N V_N* on ran(V_N), zero on its orthogonal complement"
            ),
            "exact_resolvent": (
                "(H_N-z)^(-1)=-z^(-1)(I-V_NV_N*)+"
                "V_N(L_N-z)^(-1)V_N*"
            ),
            "route": [
                "stable causal rows and summable carry tails give T_N -> T strong-star",
                "uniform lower/upper frame bounds give F_N^(-1/2) -> F^(-1/2) strongly",
                "therefore V_N -> V strong-star and V_NV_N* -> VV* strongly",
                "the diagonal resolvents (L_N-z)^(-1) converge strongly",
                "the exact formula gives strong-resolvent convergence H_N -> H",
            ],
            "mosco_note": (
                "Mosco/Trotter-Kato is an alternative formulation. It is not "
                "needed for the full transported generator because its "
                "resolvent is explicit. It may still be useful for the bulk "
                "compression and the boundary relation."
            ),
        },
        "source_material_assessment": {
            "convergence_document": (
                "/home/thlinux/mersenne/docs/"
                "E_esse_CONVERGENCIA_RESOLVENTE_L_HMOTTA.md"
            ),
            "useful_piece": (
                "The Mosco-form -> Trotter-Kato -> resolvent route is the "
                "correct general framework."
            ),
            "not_reused_as_proof": (
                "Its grid regularity, approximate independence, and spectral-"
                "zero conclusions are asserted rather than established and "
                "belong to a different prime/2-adic model."
            ),
            "c2_resolvent_documents": [
                "/home/thlinux/operador_c2/Arquivo/"
                "A001_bloco_canonico_resolventes_c_2.md",
                "/home/thlinux/operador_c2/Arquivo/"
                "resolvente_do_operador_c₂_e_cancelamento_espectral_"
                "formulacao_rigorosa.md",
                "/home/thlinux/operador_c2/Arquivo/"
                "A002_complete_c2_operator_spectral_resolvent.md",
            ],
            "reused_distinction": (
                "A positive radial/vertical resolvent cannot select native "
                "zeros by itself; phase cancellation remains in the t-dependent "
                "characteristic. Operator resolvents and arithmetic Dirichlet "
                "generating functions must not be conflated."
            ),
        },
        "cutoff_audits": rows,
        "boundary_status": {
            "full_self_adjoint_limit": (
                "candidate H=V L V* direct-sum zero on the gauge complement"
            ),
            "bulk_and_weyl": (
                "local numerical convergence is observed; a closed quadratic-"
                "form/Mosco proof for H_BB,N remains to be written"
            ),
            "ordinary_boundary_triple": (
                "not yet identified; the finite Schur family is already a "
                "self-adjoint colligation/Feshbach realization, while the "
                "infinite densely-defined symmetric restriction still needs "
                "a domain and Green identity"
            ),
        },
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sizes", default="16,32,64,128,256")
    parser.add_argument("--probe-support", type=int, default=8)
    parser.add_argument("--output", type=Path)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    if args.probe_support < 1:
        parser.error("probe-support must be positive")
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
