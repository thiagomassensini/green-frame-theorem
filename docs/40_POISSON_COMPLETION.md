# Parseval and Poisson completion

A `NormalizedAnalysis` is a real linear isometry, so it preserves norm exactly. The Poisson layer is expressed by `PoissonData`:

```text
external : H → E
bulk : H → B
leftInverse : E → H
leftInverse ∘ external = id.
```

The canonical algebraic return is `poissonOperator = bulk ∘ leftInverse`. Lean proves the exact operator identity

```text
poissonOperator ∘ external = bulk.
```

The coherent full range is exactly the graph of that return over the compatible external range. A nonzero coherent bulk coordinate forces both the bulk map and the Poisson map to be nonzero.
