# Poisson instance-scope audit trigger

This branch-only marker reruns the full Lean and trust gate after isolating the `PoissonData` definition scope from its theorem namespace, removing overlapping-instance and unused-section-variable warnings without changing any theorem statement.
