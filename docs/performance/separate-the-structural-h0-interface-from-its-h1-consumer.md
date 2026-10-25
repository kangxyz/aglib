> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#separate-the-structural-h0-interface-from-its-h1-consumer) · [Context](original-context.md) · [Case index](README.md) · [Previous record](preserve-exact-import-casing-across-native-platforms.md) · [Next record](retain-the-given-grading-in-an-exceptional-chart-quotient.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Separate the structural H0 interface from its H1 consumer

The closed-embedding `UnitTrace` consumer needs the original structure
section map, coefficient module, unit and H0 comparison, together with the
literal derived pushforward unit. Importing the full `Proper.DerivedStructure`
also forced its separate Postnikov, Leray and H1 proofs into that dependency
path. In `remote-38af34a7`, the then-current Main failed after 266 seconds and the
UnitTrace body was not reached.

Move those shared definitions and H0 results into the focused
[DerivedStructure.Basic](../../Aglib/AlgebraicGeometry/Cohomology/Proper/DerivedStructure/Basic.lean),
preserving their names, original maps and hypotheses. Keep the H1 argument
and its additional comparison dependencies in the original Main module.
Import Basic and the actual single-unit provider directly from UnitTrace.
The existing native graph `remote-5c7a586b` built Basic `cc0f7917` in 6.2
seconds and reached the full UnitTrace `631a4edf` body independently while
Main `d095dd72` still failed. UnitTrace then reported its own repairable
compiler errors.

This records a passed lower interface and an unblocked independent consumer,
not a UnitTrace pass or a measured speedup of the complete proof. The same
batch still contains the independent H1 target; no per-layer build barrier,
budget increase or extra diagnostic run is needed.

