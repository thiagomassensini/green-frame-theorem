# Arithmetic partition layer

The abstract input is a finite family of nonnegative camera weights with total mass one. This is the exact part of the paper proof used by the frame estimate after the arithmetic carry construction has produced the weights.

`AdmissibleCameraPartition` stores the weight, nonnegativity, and normalization. `normalizedWeight` constructs such weights from arbitrary nonnegative activities with positive total activity. The kernel proves nonnegativity, support behavior, normalization, and the pointwise upper bound `ω_i ≤ 1`.

The canonical witness at `n=4` is represented by two equal activities, corresponding to bases `2` and `4`; both normalized weights are exactly `1/2`.
