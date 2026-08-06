# All-Bases Green Frame Theorem

Lean 4 formalization of a carry-weighted arithmetic frame built from all positional bases, with a Pythagorean Green–return split, explicit frame bounds, Parseval normalization, exact Poisson reconstruction of the coherent Green bulk, and a nontrivial `(base, number) = (2, 4)` witness.

## Kernel build

```bash
lake build --wfail GreenFrame
```

The public root imports 14 Lean modules and exposes 41 named theorems. The repository contains no `sorry`, `admit`, custom `axiom`, or `unsafe` declaration.

## Scope

The formalized theorem is independent of primality, special-function zeros, analytic continuation, functional equations, and conjectural spectral assertions. The complex notation used in related numerical laboratories is not required by this formal core.
