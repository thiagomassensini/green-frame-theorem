# Concrete reconstruction contract

This branch reconstructs the formalization that was previously reported green locally but was not persisted.

## Remote-first rule

Every logical layer is committed to this GitHub branch before the next layer begins. GitHub Actions, not an ephemeral checkout, is the publication witness. Failed iterations remain in history and are corrected by follow-up commits.

## Required mathematical result

The official release must contain a concrete all-bases Green frame over a real or complex ℓ² state space, including:

1. positional carry depth and the canonical log-depth partition, with an exact `(2,4)` witness;
2. the Green/residual Pythagorean split;
3. a concrete Green analysis map and a global Bessel bound obtained from current/parent/grandparent reindexing;
4. the full analysis frame bounds `1/2` and an explicit universal upper constant;
5. the frame operator, invertibility or an equivalent kernel-checked normalization interface, and Parseval isometry;
6. external/bulk decomposition, bounded left inverse, closed external range, Poisson intertwining, and coherent graph theorem;
7. nonzero raw and normalized bulk, and nonzero Poisson operator;
8. uniform finite-section bounds and an honest statement of every limit result actually formalized.

## Publication gates

A release is prohibited until all of the following pass on the exact remote SHA:

- `lake build --wfail`;
- public theorem registry with at least 41 declarations;
- `#print axioms` for every registered theorem;
- project trust scan rejects `sorry`, `admit`, local `axiom`, and `unsafe`;
- documentation/claim ledger distinguishes exact kernel theorems from paper-only, numerical, interface, and future claims;
- source hashes and Lean-tree digest are fixed;
- release tag and assets are verified against the audited SHA.

The existing `v1.0.0` is historical test material and is not accepted as evidence for this contract.
