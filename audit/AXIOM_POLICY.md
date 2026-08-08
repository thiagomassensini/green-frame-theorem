# Axiom and trust policy

Project Lean sources may not contain `sorry`, `admit`, custom `axiom` or
`constant` declarations, `partial` or `unsafe` declarations,
`native_decide`, or `Lean.ofReduceBool`. The trust-token scan covers every byte
of every project Lean source. The declaration inventory separately covers
public `theorem` and `lemma` declarations and requires every one to occur
exactly once in `audit/theorem-registry.json`.

`GreenFrame/Audit.lean` contains one ordered `#print axioms` command for every
qualified registry name.  The audit parser checks the identity and order of
each report, not only the number of reports, and writes the canonical mapping

`GF-ID → short name → qualified name → transitive axioms`

to `audit/evidence/axiom-report.json`.

The machine-readable allowlist is `audit/axiom-allowlist.json`.  Its only
accepted Lean/Mathlib foundations are:

- `Classical.choice`;
- `Quot.sound`;
- `propext`.

Any additional axiom, missing report, duplicate report, unexpected report, or
ordering mismatch fails gate G6.  G7 independently compares the registry,
query list, and generated named report again.

The raw Lean output, canonical JSON report, allowlist, registry, logs, exact Git
identity, and their checksums are shipped in the permanent v2 release evidence.
