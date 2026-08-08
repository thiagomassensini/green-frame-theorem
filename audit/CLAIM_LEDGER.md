# Claim ledger

This table mirrors the 23 `ABGF-*` claims in section 62 of the preserved paper specification. It does not reuse a paper ID for a weaker or different Lean statement.

All 41 `GF-*` theorems in `audit/THEOREM_REGISTRY.md` are kernel-checked and axiom-audited. The coverage status below answers a separate question: how closely those theorem statements cover each paper claim.

Status vocabulary:

- `KERNEL_EXACT`: a named Lean theorem states the same claim on the represented objects.
- `KERNEL_PARTIAL`: Lean proves a proper sublemma or ingredient, not the full paper claim.
- `KERNEL_ABSTRACT`: Lean proves the conclusion only inside an assumed abstract structure or certificate; the canonical all-bases object is not constructed.
- `KERNEL_INTERFACE_ONLY`: Lean records laws of an object already supplied with the target structure; it does not construct or certify the paper object.
- `SOURCE_BOUNDARY`: the paper proof or finite evidence is preserved, but no matching Lean theorem exists in this repository.
- `FUTURE_LAYER`: deliberately excluded from this release.

| Paper ID | Paper claim | Paper status | Lean coverage | Kernel evidence and boundary |
|---|---|---|---|---|
| ABGF-AR-001 | Active canonical camera support of `n` is finite | PAPER_PROVED | SOURCE_BOUNDARY | GF-004/GF-005 describe support after an abstract `Fintype` partition is supplied; they do not prove finiteness of the canonical all-base active set. |
| ABGF-AR-002 | Canonical log-depth weights form a partition of unity | PAPER_PROVED / FINITE_EXACT | KERNEL_PARTIAL | GF-006–GF-010 prove normalization for arbitrary finite nonnegative activities with positive normalizer; the canonical log-depth instance for every `n` is absent. |
| ABGF-AR-003 | Bulk activity is at most twice depth-one activity | PAPER_PROVED | SOURCE_BOUNDARY | No matching GF theorem. GF-003/GF-010 bound an individual normalized weight by one, which is a different claim. |
| ABGF-AN-001 | The elementary atlas `A` is an isometry | PAPER_PROVED / FINITE_EXACT | KERNEL_INTERFACE_ONLY | GF-030/GF-031 take an object already typed as a `LinearIsometry`; they do not construct the paper atlas `A` or prove that construction is isometric. |
| ABGF-AN-002 | One base's horizontal channel is resolved by the remaining vertical channels | PAPER_PROVED / FINITE_EXACT | SOURCE_BOUNDARY | No matching GF theorem. |
| ABGF-GR-001 | The Green/return split satisfies `μ_G + μ_R = ω` | PAPER_PROVED / FINITE_EXACT | KERNEL_EXACT | GF-016 proves the scalar identity for every nonzero base. |
| ABGF-GR-002 | Total residual mass is at least one half | PAPER_PROVED | KERNEL_PARTIAL | GF-017 proves the per-camera inequality; no named theorem performs the canonical all-base weighted summation. |
| ABGF-GR-003 | The global stencil equals the normalized-tower TFVD | PAPER_PROVED / FINITE_EXACT | SOURCE_BOUNDARY | No matching GF theorem. GF-020–GF-022 provide only a generic three-term estimate. |
| ABGF-GR-004 | The global Green analysis satisfies `‖Gf‖² ≤ C_G ‖f‖²` | PAPER_PROVED | KERNEL_PARTIAL | GF-019–GF-022 prove a finite unweighted three-node estimate; carry weights, ancestor reindexing, the all-base operator, and the paper constant are not formalized. |
| ABGF-FR-001 | The concrete analysis `T` is a frame with bounds `1/2` and `C_F` | PAPER_PROVED / LEAN_PENDING | KERNEL_ABSTRACT | GF-023–GF-026 prove a conditional scalar ledger; GF-027/GF-028 project inequalities from an assumed `FrameCertificate`. No concrete `T` is constructed, and the kernel bound is the conservative value 13. |
| ABGF-FR-002 | `F = T*T` is positive and invertible | PAPER_PROVED / LEAN_PENDING | KERNEL_PARTIAL | GF-029 proves injectivity of a `T` already carrying a `FrameCertificate`; `F`, adjoints, positivity, and inversion are not defined. |
| ABGF-FR-003 | `V = T F^{-1/2}` is an isometry | PAPER_PROVED / FINITE_EXACT / LEAN_PENDING | KERNEL_INTERFACE_ONLY | GF-030/GF-031 expose laws of a supplied `LinearIsometry`; they do not construct `F^{-1/2}` or the normalization. |
| ABGF-PO-001 | `E₀` is bounded below | PAPER_PROVED | SOURCE_BOUNDARY | No matching normed theorem. GF-032 only projects an algebraic left inverse assumed as a field of `PoissonData`. |
| ABGF-PO-002 | `ran E₀` is closed | PAPER_PROVED | SOURCE_BOUNDARY | No matching GF theorem; the current Poisson module has no topological closed-range statement. |
| ABGF-PO-003 | `M_AB E₀ = B₀` | PAPER_PROVED / FINITE_EXACT | KERNEL_ABSTRACT | GF-033/GF-034 prove the identity for an assumed `PoissonData`, with `M` defined from the supplied left inverse; the canonical bounded operator is not constructed. |
| ABGF-PO-004 | The coherent image is the graph of `M_AB` | PAPER_PROVED | KERNEL_ABSTRACT | GF-036/GF-037 prove the graph identity for an assumed `PoissonData` over the compatible external range; no canonical instance is supplied. |
| ABGF-BK-001 | The canonical bulk is nonzero | PAPER_PROVED / FINITE_EXACT | KERNEL_PARTIAL | GF-011–GF-013 normalize a hard-coded two-entry equal-activity chart intended to model `(2,4)`; they do not encode `n=4`, bases 2/4, positional depth, or the index-to-base correspondence. GF-038 then derives map nonzeroness from an assumed nonzero bulk witness, with no canonical bulk-coordinate connection. |
| ABGF-BK-002 | `‖B₀‖² ≥ 1/(4 C_F)` | PAPER_PROVED | SOURCE_BOUNDARY | No matching quantitative GF theorem. GF-039 gives only qualitative Poisson nonzeroness from an assumed nonzero bulk witness. |
| ABGF-FS-001 | Finite sections `T_N` have uniform frame bounds | PAPER_PROVED | KERNEL_PARTIAL | GF-040 restates pointwise scalar bounds after all four component inequalities are assumed; no `T_N` or finite-section operator is constructed. |
| ABGF-FS-002 | `T_N → T` strongly | PAPER_PROVED | SOURCE_BOUNDARY | No matching GF theorem. GF-041 assumes scalar `Tendsto` and only transports interval bounds after convergence is given; it proves no part of the operator convergence claim. |
| ABGF-FS-003 | `V_N → V` strongly | PAPER_ARGUMENT / LEAN_PENDING | SOURCE_BOUNDARY | No matching GF theorem. |
| ABGF-FS-004 | `M_N → M_AB` strongly | FUTURE_LAYER | FUTURE_LAYER | No matching GF theorem; intentionally deferred. |
| ABGF-WEYL-001 | Weyl family from the Schur complement of the `log n` generator | FUTURE_LAYER | FUTURE_LAYER | No matching GF theorem; intentionally deferred. |
