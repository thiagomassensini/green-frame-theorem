# Claim ledger

Status vocabulary:

- `PAPER_PROVED`: proved in `docs/90_PAPER_SPECIFICATION.md`.
- `KERNEL_TARGET`: represented by a named Lean theorem, awaiting the exact CI head result.
- `KERNEL_CHECKED`: may be used only after the pinned build and axiom audit pass.
- `FINITE_EXACT`: independently implemented as an exact finite identity.
- `NUMERIC_AUDITED`: numerical evidence only.
- `FUTURE_LAYER`: deliberately excluded from this release.

| ID | Claim | Paper | Lean v1.0.0 target |
|---|---|---:|---:|
| ABGF-AR-001 | Active camera support is finite | PAPER_PROVED | source boundary |
| ABGF-AR-002 | Nonnegative normalized activities sum to one | PAPER_PROVED | KERNEL_TARGET |
| ABGF-AR-003 | Every admissible weight is at most one | PAPER_PROVED | KERNEL_TARGET |
| ABGF-GR-001 | `μ_G + μ_R = ω` | PAPER_PROVED | KERNEL_TARGET |
| ABGF-GR-002 | Residual mass is at least one half | PAPER_PROVED | KERNEL_TARGET |
| ABGF-GR-003 | Green mass is at most one half | PAPER_PROVED | KERNEL_TARGET |
| ABGF-GR-004 | Finite Green analysis obeys a Bessel estimate | PAPER_PROVED | KERNEL_TARGET |
| ABGF-FR-001 | Scalar full-energy frame ledger | PAPER_PROVED | KERNEL_TARGET |
| ABGF-FR-002 | A certified full analysis is injective | PAPER_PROVED | KERNEL_TARGET |
| ABGF-FR-003 | Parseval-normalized analysis preserves norm | PAPER_PROVED | KERNEL_TARGET |
| ABGF-PO-001 | External synthesis is a left inverse | PAPER_PROVED | KERNEL_TARGET |
| ABGF-PO-002 | Exact Poisson intertwining `ME=B` | PAPER_PROVED | KERNEL_TARGET |
| ABGF-PO-003 | Coherent range equals the Poisson graph | PAPER_PROVED | KERNEL_TARGET |
| ABGF-BK-001 | Canonical weight `ω₂(4)=1/2` | PAPER_PROVED | KERNEL_TARGET |
| ABGF-BK-002 | Nonzero bulk implies nonzero Poisson return | PAPER_PROVED | KERNEL_TARGET |
| ABGF-FS-001 | Cutoff frame bounds are uniform | PAPER_PROVED | KERNEL_TARGET |
| ABGF-FS-002 | Closed bounds pass to convergent limits | PAPER_PROVED | KERNEL_TARGET |
| ABGF-CAN-001 | Full canonical all-base positional-depth instance | PAPER_PROVED | source boundary |
| ABGF-CAN-002 | Sharp paper constant `C_F≈10.8453795` | PAPER_PROVED | documented; conservative kernel bound 13 |
| ABGF-WEYL-001 | Spectral Weyl family | FUTURE_LAYER | excluded |
