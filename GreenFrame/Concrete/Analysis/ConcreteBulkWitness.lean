import GreenFrame.Concrete.Analysis.ConcreteBulkWitnessTransfer

/-!
# Canonical quantitative paper-bulk witness at `(base,number) = (2,4)`

Thin public aggregator for the mechanically split checkpoint chain:

* `ConcreteBulkWitnessArithmetic` fixes the event and delta state;
* `ConcreteBulkWitnessCoordinates` evaluates the exact Green coordinate;
* `ConcreteBulkWitnessRaw` proves the raw `G≥2` lower bound;
* `ConcreteBulkWitnessTransfer` performs the CFC/Poisson transfer.

The declaration order and public theorem names are unchanged from the
monolithic draft.
-/
