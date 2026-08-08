# Frame theorem core

The scalar frame ledger separates the external residual/seed energy from Green energy. If

```text
(1/2) state ≤ residualSeed ≤ state
0 ≤ green ≤ greenBoundConstant * state,
```

then the full energy lies between `(1/2) state` and `fullFrameBound * state`.

`FrameCertificate` transports the resulting inequalities to a continuous linear analysis map. Its positive lower bound proves injectivity. The paper specification gives the sharper universal constant

```text
C_F = 1 + 3/2 + 12 Σ_{b≥2} b⁻² + 3 Σ_{b≥2} b⁻³
    ≈ 10.8453795116575.
```

The recovered Lean core presently uses the conservative rational constants `greenBoundConstant = 12` and `fullFrameBound = 13`, which dominate the same scalar ledger without importing a special-function evaluation.
