# Release audit v2

The official v2 evidence is tied to one Git commit and one Git tree.  Counts
are discovered from versioned manifests and the repository itself; no legacy
success total is accepted as a substitute.

## Seven gates

1. Revision identity and reproducibility.
2. Repository trust, public registry, documentation inventory, and the exact
   23-claim release boundary: 20 kernel, one named conditional implication,
   one evidence-free open claim, and one evidence-free future layer.
3. Exact integrity of the 16 preserved research inputs.
4. Complete public import closure rooted at `GreenFrame.lean`.
5. Warning-free build of the public root.
6. Ordered, exact-identity kernel axiom report for every registry entry.
7. Cross-consistency of every identity and count above.

The release contract also fixes the exact SHA-256 of the 23-row machine
ledger, its GF-494 registry count, status summary, coefficient split and
canonical `(base,n)=(2,4)` witness. G2 and G7 independently reject drift in
those fields. The publisher compares the ledger, theorem-registry and research
manifest digests from the audited assets with the exact checkout before any
write-capable release action.

The generated `audit/evidence/audit-manifest.json` records the commit, tree,
parents, Lean/Mathlib versions, workflow/run identity, dynamic counts, trust
allowlist/usage, claim coverage, gate results, and SHA-256 of the component
evidence. Publisher manifests also preserve the verified upstream run's head,
status, conclusion, event, branch, workflow, attempt, timestamps, and URL.
Lean, Mathlib and third-party Actions are immutably pinned. The hosted
`ubuntu-24.04` runner label is not an immutable machine image, so the manifest
records the concrete runner image/version identifiers exposed by Actions and
the runtime instead of claiming that part of the environment is permanently
fixed.

## Persistence

Pull-request and main-branch workflows upload a 90-day diagnostic artifact.
That artifact is not the permanent publication.  The v2 publisher reruns the
same gates on the exact main SHA in a read-only job. A separate write-capable
job receives only the six audited assets, creates a release draft, verifies
every uploaded byte, creates and peels the exact-target annotated tag whose
message binds the SHA-256 of `SHA256SUMS.txt`, then publishes the draft. It
re-downloads the published assets before completing. A pre-existing published
release is accepted by the read-only route only if that tag binding, the exact
five-record checksum manifest, the run-bound audit manifest, and all six assets
agree.
The tagger name/email are fixed by the release contract and its timestamp is
the target commit's committer timestamp; all three are rechecked on recovery
and after publication.

A draft already carrying the exact annotated tag follows a separate recovery
route: its existing run-bound assets and tag binding are revalidated read-only,
the audit is not rebuilt under a different run identity, and the write job may
only finish the already-verified publication.
The GitHub release assets are the permanent audit bundle.

## Publication authorization

The publisher has two fail-closed entry paths:

- a manual dispatch from `refs/heads/main`, carrying the exact target SHA,
  first parent SHA, and successful `lean-audit.yml` run ID;
- creation or fast-forward update of `publish-v2.0.0-trigger` so it
  points directly at the exact current `main` SHA, with no marker commit.

For the trigger path, the read-only job derives the target's first parent and
selects the newest successful `push/main` run of `lean-audit.yml` whose head
is that same SHA. It waits for that audit when necessary. The trigger ref,
`main`, checkout, event SHA, workflow-definition SHA, first parent, and
upstream audit head must all agree before any write-capable job can start.

The manual path additionally compares all three supplied inputs with the same
derived identities. Branch-selected workflow definitions, marker commits,
merge refs, unverified tags, and Actions evidence from another SHA are
rejected.
