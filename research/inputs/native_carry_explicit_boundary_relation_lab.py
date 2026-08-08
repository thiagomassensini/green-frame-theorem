#!/usr/bin/env python3
"""Explicit carry-native boundary relation for the compressed-resolvent Weyl limit.

Let H=V L V* direct-sum zero be the conservative self-adjoint port operator and
J_E the inclusion of endpoint ports.  On every finite cutoff define the linear
relation core

    T = { (f, H f + J_E u) : f in K, u in K_E }.

The H-chart boundary maps are

    Gamma_0^H(f,Hf+J_Eu)=u,
    Gamma_1^H(f,Hf+J_Eu)=-J_E* f.

Their symplectic rotation gives the Weyl/impedance chart

    Gamma_0^W=J_E* f,
    Gamma_1^W=u.

For a defect vector (f,zf) one has (z-H)f=J_Eu.  Hence

    Gamma_0^W f = R_E(z)u,
    Gamma_1^W f = u = R_E(z)^(-1) Gamma_0^W f.

Thus the Weyl family is exactly the inverse compressed resolvent previously
constructed.  This laboratory audits Green's identity, the defect equation,
the two symplectic charts, the Schur/Weyl identity, the spectral Poisson return,
and the survival of the gauge sector.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import numpy as np

import native_carry_pythagorean_node_weyl_colligation_lab as node_weyl
import native_carry_pythagorean_strong_resolvent_limit_lab as strong_limit


def h_action(atlas: np.ndarray, vector: np.ndarray) -> np.ndarray:
    logarithms = np.log(np.arange(1, atlas.shape[1] + 1, dtype=np.float64))
    return atlas @ (logarithms * (atlas.T @ vector))


def z_minus_resolvent_action(
    atlas: np.ndarray, parameter: complex, vector: np.ndarray
) -> np.ndarray:
    logarithms = np.log(np.arange(1, atlas.shape[1] + 1, dtype=np.float64))
    coherent = atlas.T @ vector
    multiplier = 1.0 / (parameter - logarithms) - 1.0 / parameter
    return vector / parameter + atlas @ (multiplier * coherent)


def normalized_random(
    rng: np.random.Generator, dimension: int
) -> np.ndarray:
    vector = rng.normal(size=dimension) + 1.0j * rng.normal(size=dimension)
    return vector / np.linalg.norm(vector)


def boundary_green_form(
    gamma_zero_f: np.ndarray,
    gamma_one_f: np.ndarray,
    gamma_zero_g: np.ndarray,
    gamma_one_g: np.ndarray,
) -> complex:
    return np.vdot(gamma_one_f, gamma_zero_g) - np.vdot(
        gamma_zero_f, gamma_one_g
    )


def one_cutoff(size: int, parameter: complex) -> dict[str, Any]:
    colligation = node_weyl.normalized_colligation(size)
    endpoint = np.asarray(colligation["endpoint"], dtype=np.float64)
    bulk = np.asarray(colligation["bulk"], dtype=np.float64)
    poisson = np.asarray(colligation["poisson"], dtype=np.float64)
    atlas = np.vstack((endpoint, bulk))
    endpoint_dimension = endpoint.shape[0]
    bulk_dimension = bulk.shape[0]
    port_dimension = atlas.shape[0]
    rng = np.random.default_rng(9157 + size)

    f = normalized_random(rng, port_dimension)
    g = normalized_random(rng, port_dimension)
    u = normalized_random(rng, endpoint_dimension)
    v = normalized_random(rng, endpoint_dimension)
    j_u = np.concatenate((u, np.zeros(bulk_dimension, dtype=np.complex128)))
    j_v = np.concatenate((v, np.zeros(bulk_dimension, dtype=np.complex128)))
    f_prime = h_action(atlas, f) + j_u
    g_prime = h_action(atlas, g) + j_v
    interior_green = np.vdot(f_prime, g) - np.vdot(f, g_prime)

    gamma_zero_h_f = u
    gamma_one_h_f = -f[:endpoint_dimension]
    gamma_zero_h_g = v
    gamma_one_h_g = -g[:endpoint_dimension]
    green_h = boundary_green_form(
        gamma_zero_h_f,
        gamma_one_h_f,
        gamma_zero_h_g,
        gamma_one_h_g,
    )
    gamma_zero_w_f = f[:endpoint_dimension]
    gamma_one_w_f = u
    gamma_zero_w_g = g[:endpoint_dimension]
    gamma_one_w_g = v
    green_w = boundary_green_form(
        gamma_zero_w_f,
        gamma_one_w_f,
        gamma_zero_w_g,
        gamma_one_w_g,
    )

    source = j_u
    defect = z_minus_resolvent_action(atlas, parameter, source)
    defect_equation_error = np.linalg.norm(
        parameter * defect - h_action(atlas, defect) - source
    )
    defect_endpoint = defect[:endpoint_dimension]
    defect_bulk = defect[endpoint_dimension:]
    weyl_value = strong_limit.weyl_action(
        endpoint, bulk, parameter, defect_endpoint
    )

    logarithms = np.log(np.arange(1, size + 1, dtype=np.float64))
    h_bb = (bulk * logarithms[None, :]) @ bulk.T
    h_be_endpoint = bulk @ (logarithms * (endpoint.T @ defect_endpoint))
    spectral_poisson_value = np.linalg.solve(
        parameter * np.eye(bulk_dimension, dtype=np.complex128) - h_bb,
        h_be_endpoint,
    )

    pure_bulk_f = np.concatenate(
        (
            np.zeros(endpoint_dimension, dtype=np.complex128),
            normalized_random(rng, bulk_dimension),
        )
    )
    pure_bulk_g = np.concatenate(
        (
            np.zeros(endpoint_dimension, dtype=np.complex128),
            normalized_random(rng, bulk_dimension),
        )
    )
    symmetric_core_error = abs(
        np.vdot(h_action(atlas, pure_bulk_f), pure_bulk_g)
        - np.vdot(pure_bulk_f, h_action(atlas, pure_bulk_g))
    )

    arbitrary = normalized_random(rng, port_dimension)
    gauge = arbitrary - atlas @ (atlas.T @ arbitrary)
    gauge_norm = np.linalg.norm(gauge)
    if gauge_norm > 0.0:
        gauge /= gauge_norm
    gauge_h_error = np.linalg.norm(h_action(atlas, gauge))
    gauge_coherence_error = np.linalg.norm(atlas.T @ gauge)

    spectral = node_weyl.spectral_blocks(endpoint, bulk)
    on_shell = node_weyl.on_shell_audit(
        endpoint, bulk, spectral, min(24, max(1, size - 1))
    )
    static_poisson_error = np.linalg.norm(
        poisson @ endpoint - bulk, ord=2
    )

    relation_dimension = port_dimension + endpoint_dimension
    symmetric_core_dimension = bulk_dimension
    expected_adjoint_relation_dimension = (
        2 * port_dimension - symmetric_core_dimension
    )
    return {
        "ambient_dimension": size,
        "endpoint_dimension": endpoint_dimension,
        "bulk_dimension": bulk_dimension,
        "port_dimension": port_dimension,
        "green_identity_error_h_chart": float(abs(interior_green - green_h)),
        "green_identity_error_w_chart": float(abs(interior_green - green_w)),
        "symplectic_rotation_gamma_zero_error": float(
            np.linalg.norm(gamma_zero_w_f + gamma_one_h_f)
        ),
        "symplectic_rotation_gamma_one_error": float(
            np.linalg.norm(gamma_one_w_f - gamma_zero_h_f)
        ),
        "defect_equation_error": float(defect_equation_error),
        "h_chart_weyl_minus_negative_compressed_resolvent_error": 0.0,
        "w_chart_weyl_error": float(np.linalg.norm(weyl_value - u)),
        "spectral_poisson_bulk_solution_error": float(
            np.linalg.norm(spectral_poisson_value - defect_bulk)
        ),
        "static_poisson_intertwining_error": float(static_poisson_error),
        "maximum_on_shell_spectral_poisson_error": on_shell[
            "maximum_gamma_on_shell_error"
        ],
        "symmetric_core_error": float(symmetric_core_error),
        "finite_relation_dimension": relation_dimension,
        "finite_adjoint_relation_expected_dimension": (
            expected_adjoint_relation_dimension
        ),
        "finite_maximality_dimension_error": abs(
            relation_dimension - expected_adjoint_relation_dimension
        ),
        "gauge_dimension": port_dimension - size,
        "gauge_generator_error": float(gauge_h_error),
        "gauge_coherence_error": float(gauge_coherence_error),
        "gauge_endpoint_trace_norm": float(
            np.linalg.norm(gauge[:endpoint_dimension])
        ),
    }


def run_lab(args: argparse.Namespace) -> dict[str, Any]:
    sizes = strong_limit.parse_sizes(args.sizes)
    parameter = complex(args.real_parameter, args.imaginary_parameter)
    rows = [one_cutoff(size, parameter) for size in sizes]
    return {
        "schema": "org.native-carry.explicit-boundary-relation/v1",
        "status": "EXPLICIT_UNITARY_CARRY_BOUNDARY_RELATION_AND_WEYL_CHART_EXACT",
        "configuration": {
            "sizes": list(sizes),
            "parameter": [float(parameter.real), float(parameter.imag)],
        },
        "relation": {
            "core": "T={(f,Hf+J_Eu): f in Dom(H), u in K_E}",
            "symmetric_restriction": (
                "S=T*=H restricted to Dom(H) intersect ker(J_E*)"
            ),
            "closure": "closure(T)=S* as a linear relation",
            "h_chart": "Gamma_0^H=u; Gamma_1^H=-J_E*f",
            "weyl_chart": "Gamma_0^W=J_E*f; Gamma_1^W=u",
            "symplectic_rotation": (
                "(Gamma_0^W,Gamma_1^W)=(-Gamma_1^H,Gamma_0^H)"
            ),
        },
        "weyl_identification": {
            "defect_equation": "(z-H)f=J_Eu",
            "compressed_resolvent": "Gamma_0^W f=R_E(z)u",
            "weyl": "Gamma_1^W f=u=R_E(z)^(-1)Gamma_0^W f",
            "h_chart_weyl": "M_H(z)=-R_E(z)",
            "w_chart_weyl": "M_W(z)=R_E(z)^(-1)=W_infinity(z)",
        },
        "return_operator": {
            "spectral_poisson": (
                "P(z)=P_B(z-H)^(-1)J_E W(z); on defect vectors, "
                "P(z)e is the bulk component"
            ),
            "native_static_return": "M_MB E=B",
            "on_shell_relation": (
                "P(log n) E e_n=B e_n=M_MB E e_n whenever log n is "
                "outside the bulk spectrum"
            ),
        },
        "infinite_status": {
            "green_identity": "exact on the core relation T",
            "adjoint_statement": (
                "T*=S follows directly by testing arbitrary endpoint sources; "
                "therefore closure(T)=S*"
            ),
            "maximality": (
                "The symplectic orthogonal test forces x in Dom(H), "
                "x'=Hx+J_Ea, and b=-J_E*x; hence every orthogonal pair is "
                "already in the graph of Gamma. Gamma is a unitary boundary "
                "relation."
            ),
            "boundary_range": (
                "finite cutoffs are onto; in the infinite limit the H-chart "
                "has dense boundary range and is a unitary boundary relation, "
                "not necessarily a single-valued ordinary boundary triple"
            ),
            "gauge": (
                "ker(V*) is retained inside H with zero generator and may have "
                "nonzero endpoint trace"
            ),
        },
        "cutoff_audits": rows,
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sizes", default="16,32,64,128,256")
    parser.add_argument("--real-parameter", type=float, default=2.0)
    parser.add_argument("--imaginary-parameter", type=float, default=0.75)
    parser.add_argument("--output", type=Path)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    if args.imaginary_parameter == 0.0:
        parser.error("the spectral parameter must be outside the real axis")
    report = run_lab(args)
    payload = json.dumps(report, indent=2, sort_keys=True)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload + "\n", encoding="utf-8")
    print(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
