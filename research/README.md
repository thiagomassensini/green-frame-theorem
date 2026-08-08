# Research inputs

These files are the user-supplied mathematical notes and computational laboratories used to reconstruct the official Green Frame formalization.

They are preserved byte-for-byte under `research/inputs/`. Their SHA-256 digests are fixed in `SOURCE_MANIFEST.md`.

Trust boundary:

- Markdown proofs are the mathematical specification, not kernel evidence.
- Python laboratories are finite or numerical evidence, not kernel evidence.
- Only declarations reachable from `GreenFrame.lean`, built by pinned Lean/Mathlib with `--wfail`, and listed by the axiom audit may be classified as `KERNEL_CHECKED`.
- Spectral, strong-resolvent, Weyl, colligation, and camera-completeness material stays outside the theorem release unless independently formalized.
