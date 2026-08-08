# Scope and trust boundary

The project has two explicitly separated layers.

1. **Paper theorem.** `docs/90_PAPER_SPECIFICATION.md` contains the complete mathematical construction on the all-bases carry atlas: log-depth weights, the split `μ_G=ω/b`, `μ_R=ω(1-1/b)`, the Green Bessel bound, the frame operator, Parseval normalization, Poisson completion, nontrivial bulk, and finite-section convergence.
2. **Lean kernel core.** The Lean modules prove the reusable finite-partition, scalar-ledger, linear-isometry, exact-left-inverse, graph, and limit lemmas registered in `audit/THEOREM_REGISTRY.md`.

The claim ledger is authoritative. A paper statement is not promoted to `KERNEL_EXACT` merely because a related or conditional `GF-*` theorem compiles. Numerical laboratories are provenance and regression evidence only.

Excluded from the `v1.0.x` audited core: zero loci, special functions, analytic continuation, a logarithmic generator, spectral Weyl functions, and maximal self-adjoint extensions.
