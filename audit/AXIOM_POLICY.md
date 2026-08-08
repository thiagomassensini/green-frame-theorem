# Axiom and trust policy

Project sources may not contain `sorry`, `admit`, custom `axiom`, or `unsafe` declarations.

Every theorem in `audit/theorem-registry.json` is queried with `#print axioms`. The only accepted transitive axioms are the standard Lean/Mathlib foundations:

- `propext`
- `Quot.sound`
- `Classical.choice`

The generated CI log is published as an audit artifact and packaged with the release evidence.
