# Source provenance

## Preserved research corpus

The 16 user-supplied mathematical notes and computational laboratories are
preserved byte-for-byte under `research/inputs/`.  The authoritative filenames
and SHA-256 digests are versioned in `research/source-manifest.json`; the human
table is `research/SOURCE_MANIFEST.md`.

Gate G3 requires all of the following:

- the contract, JSON manifest, and actual directory contain the same count;
- the directory has exactly the manifested filenames, with no extra or missing
  regular file and no symlink;
- every byte digest matches its manifest entry;
- the human manifest contains every filename and digest exactly once;
- the legacy materialized paper is byte-identical to the primary input.

The primary mathematical source is
`TEOREMA_FRAME_GREEN_TODAS_AS_BASES.md`, SHA-256
`366dfa007002c1d3dbf2eb7c283c13c1b35233647163753ee39e45dd0645c3f4`.

## Trust boundary

Markdown proofs are the mathematical specification.  Python laboratories are
finite or numerical evidence.  Neither is a Lean proof dependency.  Only
registered declarations in the public import closure that pass the pinned
kernel build and named axiom audit may back the 20 unconditional
`KERNEL_CHECKED` claims.  The `CONDITIONAL` FS-003 row cites a kernel-audited
implication but leaves its stated CFC hypothesis open; it is not counted among
the 20 unconditional claims.  FS-004 remains `OPEN`, and Weyl remains
`FUTURE_LAYER`, both without theorem evidence.

## Generated evidence

`audit/evidence/source-provenance.json` records the verified source set and
digests for the exact audit run.  The audit manifest hashes that report.  Both
are included in the checksummed, permanent v2 release bundle.

## Recovery provenance

The formerly reported local SHA
`3ca1c5394f7f6ff38064496e67750efacc0c70fb` was not available in the remote Git
object database.  The v2 release therefore identifies only the newly
reconstructed remote commit/tree and its exact GitHub Actions runs; it does not
represent the unavailable object as recovered.
